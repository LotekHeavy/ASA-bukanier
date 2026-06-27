#!/usr/bin/env python3
# Version
# 1.01 Initial Version
# 1.02 backupdb für mariadb im docker hinzugefügt
# 1.03 rotationmap hinzugefügt
# 1.04 shop --get stoppt den server nicht mehr, sondern macht nur saveworld
# 1.05 Zufall neu auf SWWR basierend
# 1.06 Playernummer von listpalyers optimiert
# 
# -----------------------------------------------------------------------------
# Core-Protokoll: ARK Survival Ascended Cluster-Management
# -----------------------------------------------------------------------------
# Beschreibung:
# Zentrales Interface-Skript zur Orchestrierung von ASA-Docker-Instanzen.
# Steuert den kompletten Server-Lifecycle, synchronisiert Datenströme im Cluster
# und automatisiert Wartungsroutinen.
#
# Kernfunktionen:
# - Lifecycle: Start, Restart und sauberer Stop (RCON doexit + Countdown-Warnung)
# - Orchestrierung: Ausführung auf Einzel-Knoten oder definierten Server-Gruppen
# - Deployment: Synchronisation von INIs (inkl. Include-Logik), API, Whitelist & Banlist
# - Backups: Map-Synchronisation, Full-Archivierung (tar.gz) und MariaDB-Dumps
# - Subsysteme: Map-Rotation (Smooth Weighted Round-Robin) direkt im Compose-File
# - Event-Management: Dynamische Injektion von Mod-IDs und DynamicConfig-Presets
# - Interaktion: RCON-Konsole, Live-Logs, Player-Tracking und Cross-Server Shop-Sync
# -----------------------------------------------------------------------------

import sys
import re
import os
import json
import subprocess
import random
import requests
import time
import shutil
import tempfile
from datetime import datetime, timedelta
from typing import List, Dict, Set, Optional, Tuple
from math import gcd
from functools import reduce
from rich.console import Console
from rich.text import Text

console = Console()


# Persistenter State für Rotation
STATE_DIR = "/home/ark/var/rotation"
WRR_STATE_FILE = os.path.join(STATE_DIR, "rotation_wrr.json")
K_BACK = 2  # verhindert unmittelbare Wiederholung/Serien

# Konstanten
DEFAULT_KEEP_DAYS = 30
COMPOSE_FILE = "/home/ark/docker/asa/docker-compose.yml"
MARIADB = False


# Konfiguration aller gültigen Befehle und deren Eigenschaften
COMMANDS = {
    "start": {"requires_argument": False},
    "stop": {"requires_argument": False},
    "restart": {"requires_argument": False},
    "listplayers": {"requires_argument": False},
    "rcon": {"requires_argument": True},
    "deploy": {"requires_argument": False},
    "status": {"requires_argument": False},
    "backup": {"requires_argument": False},
    "backupdb": {"requires_argument": False},
    "cleanup": {"requires_argument": False},
    "saveworld": {"requires_argument": False},
    "log": {"requires_argument": False},
    "whitelist": {"requires_argument": False},
    "banlist": {"requires_argument": False},
    "shop": {"requires_argument": False},
    "bash": {"requires_argument": False},
    "xaudio": {"requires_argument": False},
    "api": {"requires_argument": True},
    "rotationmap": {"requires_argument": False},
    "event": {"requires_argument": False},
    "eventstatus": {"requires_argument": False},
    "dynamicconfig": {"requires_argument": False},
}

# Server and group mapping
servers = {
    "test": "asa-server-0",
    "island": "asa-server-1",
    "scorchedearth": "asa-server-2",
    "aberration": "asa-server-3",
    "extinction": "asa-server-4",
    "rotation": "asa-server-5",
}

# Server Gruppen
groups = {
    "home": ["island"],
    "pvp": ["scorchedearth", "aberration", "extinction"],
    "testgroup": ["test"],
    "standard": ["island", "scorchedearth", "aberration", "extinction"],
    "full": ["island", "scorchedearth", "aberration", "extinction", "rotation"],
    "all": list(servers.keys()),
}

# Konfiguration für Rotation Map (muss immer "asa-server-5" sein!!!!!)
mod_map = {
    "lostcolony":   {"id": "LostColony_WP",  "mod": None,     "weight": 1.00},
    "center":       {"id": "TheCenter_WP",   "mod": None,     "weight": 0.90},
    "ragnarok":     {"id": "Ragnarok_WP",    "mod": None,     "weight": 0.90},
    "valguero":     {"id": "Valguero_WP",    "mod": None,     "weight": 0.90},
    "astraeos":     {"id": "Astraeos_WP",    "mod": None,     "weight": 0.80},
    "svartalfheim": {"id": "Svartalfheim_WP","mod": "962796", "weight": 0.70},
}

class SmoothWRR:
    """
    Smooth Weighted Round-Robin (Nginx-Variante):
    - Gewichte als kleine Integer
    - current[k] = aktuelles Gewicht
    - total = Summe aller Gewichte
    """
    def __init__(self, weights: Dict[str, float], k_back: int = 1) -> None:
        self.keys: List[str] = list(weights.keys())
        # Floats → Integer skalieren und per ggT kürzen
        scaled: List[Tuple[str, int]] = []
        for k in self.keys:
            iw = max(1, int(round(weights[k] * 100)))
            scaled.append((k, iw))
        g = reduce(gcd, (w for _, w in scaled))
        self.weights: Dict[str, int] = {k: w // g for k, w in scaled}
        self.current: Dict[str, int] = {k: 0 for k in self.keys}
        self.total: int = sum(self.weights.values())
        self.last: List[str] = []
        self.k_back = max(0, k_back)

    def snapshot(self) -> Dict:
        return {
            "weights": self.weights,
            "current": self.current,
            "total":   self.total,
            "last":    self.last,
            "k_back":  self.k_back,
        }

    @staticmethod
    def from_snapshot(snap: Dict) -> "SmoothWRR":
        obj = SmoothWRR({k: float(v) for k, v in snap["weights"].items()}, k_back=snap.get("k_back", 1))
        obj.weights = {k: int(v) for k, v in snap["weights"].items()}
        obj.current = {k: int(v) for k, v in snap["current"].items()}
        obj.total   = int(snap["total"])
        obj.last    = list(snap.get("last", []))
        return obj

    def _forbidden(self) -> Set[str]:
        return set(self.last[-self.k_back:]) if self.k_back > 0 else set()

    def next(self, forbid: Optional[Set[str]] = None) -> str:
        # Schritt 1: g_i += w_i (Akkumulation der Gewichte)
        for k in self.keys:
            self.current[k] += self.weights[k]

        # Schritt 2: Selektion der erlaubten Kandidaten
        forbid_all = self._forbidden().union(forbid or set())
        candidates = [k for k in self.keys if k not in forbid_all]
        if not candidates:
            candidates = self.keys[:]  # Fallback, wenn alles verboten

        # Schritt 3: Deterministische Strenge durch Jitter brechen
        random.shuffle(candidates)
        pick = max(candidates, key=lambda k: self.current[k] + random.uniform(0, self.weights[k]))

        # Schritt 4: g_pick -= total
        self.current[pick] -= self.total

        # k-Back pflegen
        self.last.append(pick)
        if len(self.last) > self.k_back:
            self.last = self.last[-self.k_back:]

        return pick

def _ensure_state_dir() -> None:
    os.makedirs(STATE_DIR, exist_ok=True)

def _atomic_write_json(path: str, data: Dict) -> None:
    _ensure_state_dir()
    fd, tmp = tempfile.mkstemp(prefix=".wrr_", dir=STATE_DIR)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except OSError:
            pass

def _load_wrr() -> Optional[SmoothWRR]:
    try:
        with open(WRR_STATE_FILE, "r", encoding="utf-8") as f:
            snap = json.load(f)
        return SmoothWRR.from_snapshot(snap)
    except Exception:
        return None

def _save_wrr(wrr: SmoothWRR) -> None:
    _atomic_write_json(WRR_STATE_FILE, wrr.snapshot())

def _current_weights() -> Dict[str, float]:
    # Baue Gewichte dynamisch aus mod_map, dadurch sind neue Maps sofort berücksichtigt
    return {k: float(v.get("weight", 1.0)) for k, v in mod_map.items()}

def _weights_equal_int(a: Dict[str, int], b: Dict[str, int]) -> bool:
    if set(a.keys()) != set(b.keys()):
        return False
    for k in a:
        if int(a[k]) != int(b[k]):
            return False
    return True

def _normalize_int_weights(weights: Dict[str, float]) -> Dict[str, int]:
    scaled = {}
    for k, w in weights.items():
        iw = max(1, int(round(w * 100)))
        scaled[k] = iw
    g = reduce(gcd, scaled.values())
    return {k: v // g for k, v in scaled.items()}

def _map_key_from_id(map_id: str) -> Optional[str]:
    for k, v in mod_map.items():
        if v["id"] == map_id:
            return k
    return None

def _build_or_load_wrr(k_back: int = K_BACK) -> SmoothWRR:
    """Lade existierenden WRR-State. Falls Keys/Gewichte nicht mehr passen → neu aufbauen."""
    weights = _current_weights()
    desired_int = _normalize_int_weights(weights)

    existing = _load_wrr()
    if existing:
        # Prüfe, ob alle aktuellen Keys drin sind und Gewichte identisch sind
        if _weights_equal_int(existing.weights, desired_int):
            # Ergänze evtl. neu hinzugekommene Keys (sollte durch Gleichheit bereits abgedeckt sein)
            existing.keys = list(existing.weights.keys())
            existing.k_back = k_back
            return existing
        # Sonst Neuaufbau
    wrr = SmoothWRR(weights, k_back=k_back)
    return wrr

def _pick_next_map_swr(current_map_id: str) -> str:
    """
    Liefert den KURZ-Namen (Key in mod_map) der nächsten Map.
    - Schliesst die aktuelle Map aus (forbid)
    - Speichert State persistent
    """
    wrr = _build_or_load_wrr(k_back=K_BACK)

    # Verbiete aktuelle Map (über ihren Kurz-Key)
    forbid: Set[str] = set()
    cur_key = _map_key_from_id(current_map_id)
    if cur_key:
        forbid.add(cur_key)

    pick_key = wrr.next(forbid=forbid)
    _save_wrr(wrr)
    return pick_key


events = {
    "LoveAscended":    {"id": "927084", "date": None},
    "WinterWonderland":{"id": "927090", "date": None},
    "FearAscended":    {"id": "877752", "date": None},
    "SummerBash":      {"id": "927091", "date": None},
    "TurkeyTrial":     {"id": "927083", "date": None},
    "Eggcellent":      {"id": "877745", "date": None},
}

# Backup Sync (stündlicher Sync)
map_sync = [
    "TheIsland_WP.ark",
    "Ragnarok_WP.ark",
    "ScorchedEarth_WP.ark",
    "Aberration_WP.ark",
    "Extinction_WP.ark",
    "TheCenter_WP.ark",
    "Astraeos_WP.ark",
    "Svartalfheim_WP.ark",
    "Valguero_WP.ark",
    "LostColony_WP.ark",
    "*.arktribe",
    "*.arkprofile",
    "*.arkrbf",
]

DYNAMICCONFIG_PRESETS = {
    "standard": {
        "TamingSpeedMultiplier": "4.0",
        "HarvestAmountMultiplier": "1.0",
        "XPMultiplier": "1.0",
        "MatingIntervalMultiplier": "0.25",
        "MatingSpeedMultiplier": "1.0",
        "BabyMatureSpeedMultiplier": "16",
        "EggHatchSpeedMultiplier": "16",
        "BabyCuddleIntervalMultiplier": "0.1",
        "BabyImprintAmountMultiplier": "2.0",
    },
    "boosted": {
        "TamingSpeedMultiplier": "6.0",
        "HarvestAmountMultiplier": "1.0",
        "XPMultiplier": "1.0",
        "MatingIntervalMultiplier": "0.125",
        "MatingSpeedMultiplier": "2.0",
        "BabyMatureSpeedMultiplier": "24",
        "EggHatchSpeedMultiplier": "24",
        "BabyCuddleIntervalMultiplier": "0.0625",
        "BabyImprintAmountMultiplier": "2.5",
    }
}

# Hauptfunktion zur Verarbeitung von Servern und Gruppen
def process_target(command: str, target: str, rcon_command: str = None, options: List[str] = None):
    if target == "all" and command == "backupdb":
        # Backup der MariaDB nur einmal ausführen
        backupdb()
        return
    if target == "all" and command == "banlist":
        # Banlist nur einmal ausführen, da diese auf dem www zentral gespeichert wird
        deploy_banlist()
        return
    if command == "rotationmap":
        if target in mod_map:
            rotationmap(target)
        else:
            rotationmap()
        return
    if target in servers:
        server_list = [target]
    elif target in groups:
        server_list = groups[target]
    else:
        console.print(f"Unbekannter Zielname: @{target}", style="bold red")
        return

    for server in server_list:
        server_id = servers.get(server)
        if not server_id:
            console.print(f"Unbekannter Server: {server}", style="bold red")
            continue
        if command == "deploy":
            console.print(f"\n########## {server}", style="bold green")
            deploy_config(server, options)
        elif command == "start":
            start_server(server_id)
        elif command == "stop":
            warn_flag = "--warn" in (options or [])
            stop_server(server_id, warn=warn_flag)
        elif command == "restart":
            warn_flag = "--warn" in (options or [])
            restart_server(server_id, warn=warn_flag)
            time.sleep(5)
        elif command == "listplayers":
            list_players(server_id, server, 0)
        elif command == "cleanup":
            cleanup(server_id)
        elif command == "saveworld":
            saveworld(server_id)
        elif command == "log":
            log_server(server_id)
        elif command == "rcon":
            if rcon_command:
                send_rcon_command(server_id, rcon_command)
            else:
                console.print(f"Kein RCON-Befehl angegeben für {server}", style="bold red")
        elif command == "backup":
            sync_mode = "--sync" in (options or [])  # Jetzt direkt innerhalb der Backup-Prüfung
            backup(server, sync_mode)
        elif command == "backupdb":
            console.print("Fehler: Datenbank-Backup nur für @all verfügbar.", style="bold red")
        elif command == "status":
            get_status(server)
        elif command == "whitelist":
            deploy_whitelist(server)
        elif command == "xaudio":
            deploy_xaudio(server)
        elif command == "api":
            deploy_api(server, [custom_arg])
        elif command == "shop":
            deploy_shop(server, options)
        elif command == "event":
            deploy_event(server, options)
        elif command == "eventstatus":
            event_status(server)
        elif command == "dynamicconfig":
            dynamicconfig(server, options)
        elif command == "bash":
            if server not in groups:
                bash(server)
            else:
                console.print(f"Nur eine einzelne Karte ist erlaubt", style="bold red")   
                help()
                sys.exit(1)

# Validierung der finalen INI Files
def validate_ini_file(file_path: str, file_key: str):
    """
    Validiert eine INI-Datei auf Syntax, schliesst grundlegende Prüfungen und Klammernprüfung ein.
    :param file_path: Pfad zur INI-Datei, die geprüft wird.
    :param file_key: Schlüssel der aktuellen Konfiguration.
    """
    def is_balanced(value: str, pairs: list) -> bool:
        """
        Prüft, ob alle Klammern in einem String korrekt geschlossen sind.
        :param value: Der zu prüfende String.
        :param pairs: Liste von Tupeln mit öffnenden und schliessenden Zeichen.
        :return: True, wenn alle Klammern korrekt geschlossen sind.
        """
        stack = []
        for char in value:
            for open_char, close_char in pairs:
                if char == open_char:
                    stack.append(open_char)
                elif char == close_char:
                    if not stack or stack.pop() != open_char:
                        return False
        return not stack

    # Paare von Klammern
    bracket_pairs = [("(", ")"), ("[", "]"), ("{", "}")]

    try:
        with open(file_path, "r", encoding="utf-8") as file:
            for line_num, line in enumerate(file, start=1):
                stripped_line = line.rstrip("\r\n")  # Entfernt Windows-Zeilenumbrüche

                # Überspringe leere Zeilen und Kommentare
                if not stripped_line or stripped_line.startswith(";"):
                    continue

                # Prüfe auf Leerschläge am Anfang der Zeile
                if stripped_line.startswith(" "):
                    raise ValueError(
                        f"Ungültiger Leerschlag am Zeilenanfang: Zeile {line_num}: {line.strip()}"
                    )

                # Sektionen wie [Section]
                if stripped_line.startswith("[") and stripped_line.endswith("]"):
                    continue

                # Key-Value-Syntax prüfen: Muss "key=value" enthalten
                if "=" not in stripped_line:
                    raise ValueError(
                        f"Ungültige Syntax (kein '=' gefunden): Zeile {line_num}: {line.strip()}"
                    )

                # Trenne Key und Value
                key, value = stripped_line.split("=", 1)

                # Prüfe auf Leerschläge um das '='
                if key.endswith(" ") or value.startswith(" "):
                    raise ValueError(
                        f"Ungültiger Leerschlag um das '=': Zeile {line_num}: {line.strip()}"
                    )

                # Prüfe, ob der Value korrekt geschlossene Klammern enthält
                if not is_balanced(value, bracket_pairs):
                    raise ValueError(
                        f"Ungepaarte Klammern in Value: Zeile {line_num}: {line.strip()}"
                    )

                # Prüfe, ob der Value korrekt geschlossene Anführungszeichen enthält
                if value.count('"') % 2 != 0:
                    raise ValueError(
                        f"Ungepaarte Anführungszeichen in Value: Zeile {line_num}: {line.strip()}"
                    )

                # Sonderzeichen prüfen (nur ANSI-US + Umlaute erlaubt)
                if not all(
                    ord(char) < 128 or char in "äöüÄÖÜß" for char in stripped_line
                ):
                    raise ValueError(
                        f"Ungültige Zeichen in der Zeile: Zeile {line_num}: {line.strip()}"
                    )

    except Exception as e:
        console.print(f"[bold red]Fehler in {file_key}:[/bold red] {e}")
        raise
        console.print(f"Validierung abgeschlossen", style="bold green")

# Log helper
def log_message(server_name: str, message: str):
    timestamp = datetime.now().strftime("%d.%m.%Y %H:%M:%S")
    formatted_message = f"{timestamp} {server_name}: {message}"
    
    # Konsolenausgabe
    console.print(formatted_message)

    # Discord Webhook URL
    discord_webhook_url = "https://discord.com/api/webhooks/XXX"

    # Nachricht an Discord senden
    payload = {"content": formatted_message}
    try:
        response = requests.post(discord_webhook_url, json=payload)
        if response.status_code != 204:
            console.print(f"[bold red]Fehler beim Senden an Discord: {response.status_code} - {response.text}[/bold red]")
    except requests.RequestException as e:
        console.print(f"[bold red]Fehler bei der Discord Webhook-Anfrage: {e}[/bold red]")

# Execute shell command without output
def execute_command(command: List[str]) -> subprocess.CompletedProcess:
    return subprocess.run(command, text=True, capture_output=True)

# Execute shell command with output
def execute_command_with_output(command: List[str]) -> subprocess.CompletedProcess:
    result = subprocess.run(command, text=True, capture_output=True)
    if result.stdout:
        console.print(result.stdout.strip(), style="bold green")
    if result.stderr:
        console.print(result.stderr.strip(), style="bold red")
    return result

def log_server(server_id: str):
    # Docker Volume Logfile
    console.print("")
    console.print(f"#################################")
    console.print(f"Docker Volume Logfile {server_id}")
    console.print(f"#################################")
    execute_command_with_output(["docker", "logs", "-t", server_id])
    # Shootergame.log, geht nur wenn Docker Volume läuft
    console.print("")
    console.print(f"#################################")
    console.print(f"Logfile ShooterGame.log {server_id}")
    console.print(f"#################################")
    result = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
    if result.stdout.strip() == "false":
        log_message(server_id, "Docker Volume ist gestoppt")
    else:
        process = subprocess.Popen(
            ["docker", "exec", "-i", server_id, "cat", "/home/gameserver/server-files/ShooterGame/Saved/Logs/ShooterGame.log"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        for line in iter(process.stdout.readline, ''):
            console.print(line.strip())
        process.stdout.close()
        process.wait()

# Open a Bash Shell on the Server
def bash(server_name):
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: {server_name}", style="bold red")
        return
    else:
        try:
            os.execvp("docker", ["docker", "exec", "-ti", server_id, "bash"])
        except FileNotFoundError:
            console.print("Docker nicht gefunden. Ist Docker korrekt installiert?", style="bold red")

# Send server chat message
def send_server_message(server_id: str, message: str):
    current_time = datetime.now().strftime("%H:%M")
    full_message = f"{current_time} {message}"
    execute_command(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", f"ServerChat {full_message}"])

# Send generic RCON command
def send_rcon_command(server_id: str, command: str):
    result = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
    if result.returncode != 0 or result.stdout.strip() != "true":
        console.print(f"Server {server_id} läuft nicht. RCON-Befehl nicht ausgeführt.", style="bold red")
        return
    #log_message(server_id, f"Sendet RCON-Befehl: {command}")
    console.print(f"Sendet RCON-Befehl: {command}")
    execute_command_with_output(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", command])

# Speichert die Welt via RCON Befehl
def saveworld(server_id: str):
    send_rcon_command(server_id,"saveworld")
    #execute_command(["docker", "ls", temp_path, f"{server_id}:{container_path}"])

# Status vom Server via Docker inspect
def get_status(server_name):
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: {server_name}", style="bold red")
        return

    result = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
    if result.returncode != 0:
        console.print(f"Fehler beim Abrufen des Status für {server_name} ({server_id})", style="bold red")
        return

    state = result.stdout.strip()

    # Falls der Server 'rotation' ist, lese die aktuelle Karte und gebe den Kurznamen aus mod_map aus
    if server_name == "rotation" and state == "true":
        try:
            current_map = get_current_map(COMPOSE_FILE)
            # Suche den Kurzname aus mod_map basierend auf der aktuellen Karten-ID
            display_name = next((name for name, data in mod_map.items() if data["id"] == current_map), "Unbekannt")
        except Exception:
            display_name = "Unbekannt"
    else:
        display_name = server_name

    status_text = Text(f"{display_name} ({server_id}): ")
    if state == "true":
        status_text.append("Läuft", style="green")
    else:
        status_text.append("Gestoppt", style="red")
    console.print(status_text)

# Server wird via Docker gestartet
def start_server(server_id: str):
    log_message(server_id, "wird gestartet")
    result = execute_command(["docker", "start", server_id])
    
    if result.returncode != 0:
        # Fehler beim Starten
        error_message = result.stderr.strip() if result.stderr else "Unbekannter Fehler"
        log_message(server_id, f"Fehler beim Starten: {error_message}")
        console.print(f"[bold red]Fehler beim Starten von {server_id}: {error_message}[/bold red]")
    else:
        # Erfolgreich gestartet
        success_message = result.stdout.strip() if result.stdout else "Erfolgreich gestartet"
        log_message(server_id, f"Erfolgreich gestartet: {success_message}")
        console.print(f"[bold green]{server_id} erfolgreich gestartet.[/bold green]")

# Server wird zuerst saveworld, doexit und erst dann via docker gestoppt.
def stop_server(server_id: str, warn: bool = False):
    # 1. Überprüfen, ob der Server gestoppt ist
    result = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
    if result.stdout.strip() == "false":
        log_message(server_id, "Server ist bereits gestoppt")
        return

    # 2. Countdown mit Spieler-Check (Bleibt 1:1)
    countdown_shutdown(server_id, mode="stop", warn=warn)
    
    send_server_message(server_id, "Server shutdown now!")
    log_message(server_id, "speichert Welt und leitet Shutdown ein")

    # 3. Saveworld (Daten sichern)
    execute_command(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "saveworld"])
    time.sleep(4) # Puffer erhöht auf 4s, um sicherzustellen, dass Save geschrieben wird

    # 4. DoExit (Soft Stop via ARK)
    execute_command(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "doexit"])
    
    # 5. Warten auf sauberes Beenden (Polling statt Sleep)
    # Wir geben dem Server maximal 300 Sekunden Zeit, sich selbst zu beenden.
    timeout_seconds = 100
    server_stopped = False

    for _ in range(timeout_seconds):
        # Check Status
        check = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
        if check.stdout.strip() == "false":
            server_stopped = True
            log_message(server_id, "wurde sauber durch doexit beendet (Exit Code 0)")
            break
        time.sleep(3)

    # 6. Fallback: Hard Stop (Failsafe)
    # Nur ausführen, wenn der Server nach 60s immer noch läuft
    if not server_stopped:
        log_message(server_id, "reagiert nicht auf doexit - erzwinge docker stop (Exit Code 137)")
        execute_command(["docker", "stop", server_id])
    
    log_message(server_id, "ist angehalten")

# Server via saveworld, doexit beendet und dann erfolgt ein Docker neustart
def restart_server(server_id: str, warn: bool = False):
    # Countdown + vorzeitiger Abbruch, falls leer
    countdown_shutdown(server_id, mode="restart", warn=warn)
    log_message(server_id, "speichert Welt und wird neu gestartet")
    execute_command(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "saveworld"])
    time.sleep(3)
    execute_command(["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "doexit"])
    time.sleep(5)
    execute_command(["docker", "restart", server_id])


# Auflistung der aktiven Spieler
def list_players(server_id: str, server_name: str, player_counter: int) -> int:
    result = execute_command([
        "docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "listplayers"
    ])
    if result.returncode != 0:
        return player_counter

    lines = [ln.strip() for ln in result.stdout.splitlines()]
    # irrelevante Zeilen raus
    skip_fragments = (
        "no players connected",
        "players connected",    # z.B. "There are 1 players connected"
        "there are",
    )
    lines = [ln for ln in lines if ln and not any(s in ln.lower() for s in skip_fragments)]
    if not lines:
        return player_counter

    console.print(f"[bold]{server_name}:[/bold]")

    rx_strip_asa_idx = re.compile(r"^\s*\d+\.\s*")  # entfernt führendes "0. " / "12. "

    for raw in lines:
        clean = rx_strip_asa_idx.sub("", raw)

        # Optional sauber trennen: "Name, ID"
        if "," in clean:
            name, pid = [p.strip() for p in clean.split(",", 1)]
            player_counter += 1
            console.print(f"{player_counter}. {name}, {pid}")
        else:
            player_counter += 1
            console.print(f"{player_counter}. {clean}")

    return player_counter

    
def _get_online_player_count(server_id: str) -> int:
    """
    Liefert die Zahl aktuell verbundener Spieler via RCON listplayers.
    Gibt 0 zurück bei Fehler oder wenn niemand online ist.
    """
    result = execute_command(
        ["docker", "exec", "-t", server_id, "asa-ctrl", "rcon", "--exec", "listplayers"]
    )
    if result.returncode != 0 or not result.stdout:
        return 0
    lines = [l.strip() for l in result.stdout.splitlines() if l.strip()]
    players = [l for l in lines if l.lower() != "no players connected"]
    return len(players)

def _fmt_delta(seconds: int) -> str:
    return f"{seconds // 60}min" if seconds >= 60 else f"{seconds}s"

def countdown_shutdown(server_id: str, mode: str = "stop", warn: bool = False, poll_interval: int = 10) -> None:
    """
    Führt den gestaffelten Countdown nur aus, wenn warn=True.
    Ohne --warn: sofortige 0s-Meldung und Rückkehr (keine Wartezeit).
    Bricht bei warn=True vorzeitig ab, wenn keine Spieler online sind.
    """
    # Wenn kein gestaffelter Countdown gewünscht ist, sofort "0s" melden und zurück
    if not warn:
        send_server_message(server_id, "Warning! Server shutdown in 0s!")
        return

    # Nur laufen, wenn Container läuft
    state = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id]).stdout.strip()
    if state != "true":
        return

    steps = [900, 720, 600, 480, 300, 180, 120, 60, 45, 30, 15, 5, 3, 2, 1, 0]  # Sekunden

    def _fmt_delta(seconds: int) -> str:
        return f"{seconds // 60}min" if seconds >= 60 else f"{seconds}s"

    # Erste Meldung
    send_server_message(server_id, f"Warning! Server shutdown in {_fmt_delta(steps[0])}!")
    if _get_online_player_count(server_id) == 0:
        send_server_message(server_id, "No players online. Proceeding with shutdown.")
        return

    prev = steps[0]
    for next_step in steps[1:]:
        wait_total = prev - next_step
        waited = 0
        while waited < wait_total:
            chunk = min(poll_interval, wait_total - waited)
            time.sleep(chunk)
            waited += chunk
            if _get_online_player_count(server_id) == 0:
                send_server_message(server_id, "No players online. Proceeding with shutdown.")
                return
        send_server_message(server_id, f"Warning! Server shutdown in {_fmt_delta(next_step)}!")
        prev = next_step

# Clean Up Server
def cleanup(server_id: str):
    send_rcon_command(server_id, "destroywilddinos")
    #send_rcon_command(server_id, "destroyall Structure_DinoLeash_C 1"
    #send_rcon_command(server_id, "destroyall SleepingBag_C 1"
    #send_rcon_command(server_id, "destroyactors DroppedItemGeneric_FertilizedEgg_NoPhysicsWyvern_C 0")
    #send_rcon_command(server_id, "destroyactors DroppedItemGeneric_FertilizedEgg_Wyvern_C 0")
    #send_rcon_command(server_id, "destroyall WyvernNest_C 0")
    #send_rcon_command(server_id, "destroyall RockDrakeNest_C 0")
    #send_rcon_command(server_id, "destroyall BeeHive_C 1")
    #send_rcon_command(server_id; "destroytribeiddinos 2000000000")
    # cheat destroytribeiddinos 2000000000 | cheat destroywilddinos | cheat destroyactors DroppedItemGeneric_FertilizedEgg_NoPhysicsWyvern_C 0 | cheat destroyactors DroppedItemGeneric_FertilizedEgg_Wyvern_C 0 | cheat destroyall WyvernNest_C 0 | cheat destroyall RockDrakeNest_C 0 | cheat destroyall BeeHive_C 1

# Integriert die interne Banlist mit der offiziellen Banlist
def deploy_banlist():
    """
    Kombiniert die Onlinedatei mit der lokalen Banlist und erstellt eine aktualisierte Banlist.
    Das Ziel ist im Windows-Zeilenformat (CRLF).
    """
    src_file = "/home/ark/etc/banlist.txt"
    online_url = "https://cdn2.arkdedicated.com/asa/BanList.txt"
    target_file = "/var/www/ark/data/asa/banlist.txt"

    # Prüfe, ob die Quelldatei existiert
    if not os.path.exists(src_file):
        console.print(f"Fehler: Lokale Banlist-Datei {src_file} nicht gefunden.", style="bold red")
        return

    try:
        # Zieldatei löschen, falls vorhanden
        if os.path.exists(target_file):
            os.remove(target_file)

        # Lade die Onlinedatei
        console.print("Lade Onlinedatei...", style="bold green")
        response = requests.get(online_url)
        response.raise_for_status()  # Wirft eine Exception bei HTTP-Fehlern
        online_banlist = response.text.splitlines()

        # Lade die lokale Banlist
        console.print("Lese lokale Banlist ein...", style="bold green")
        with open(src_file, "r") as src:
            local_banlist = src.read().splitlines()

        # Kombiniere die beiden Listen und entferne Duplikate
        combined_banlist = set(online_banlist + local_banlist)

        # Sortiere die Einträge (optional, um Konsistenz zu gewährleisten)
        sorted_banlist = sorted(combined_banlist)

        # Schreibe die kombinierte Liste in die Zieldatei mit Windows-Zeilenenden
        console.print("Schreibe kombinierte Banlist im Windows-Format...", style="bold green")
        with open(target_file, "w", newline="\r\n") as target:
            for line in sorted_banlist:
                target.write(line + "\n")

        # Ausgabe der Zeilenanzahl
        line_count = len(sorted_banlist)
        console.print(f"Banlist erfolgreich aktualisiert. {line_count} Einträge geschrieben.", style="bold green")

    except requests.RequestException as e:
        console.print(f"Fehler beim Herunterladen der Onlinedatei: {e}", style="bold red")
    except Exception as e:
        console.print(f"Fehler beim Aktualisieren der Banlist: {e}", style="bold red")
        
# Die Whitelist wird für alle Server veröffentlicht (dieselbe)
def deploy_whitelist(server_name: str):
    """
    Kopiert die Whitelist-Datei (whitelist.txt) auf den angegebenen Server.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: @{server_name}", style="bold red")
        return

    if not server_id.startswith("asa-server-"):
        console.print(f"Ungültige Server-ID: {server_id}", style="bold red")
        return

    src_file = "/home/ark/etc/whitelist.txt"
    container_file = "/home/gameserver/server-files/ShooterGame/Binaries/Win64/PlayersJoinNoCheckList.txt"

    if not os.path.exists(src_file):
        console.print(f"Fehler: Lokale Whitelist-Datei {src_file} nicht gefunden.", style="bold red")
        return

    try:
        console.print(f"Kopiere Whitelist-Datei nach {server_name}...", style="bold green")
        execute_command(["docker", "cp", src_file, f"{server_id}:{container_file}"])
        log_message(server_name, "Whitelist erfolgreich kopiert.")
    except Exception as e:
        console.print(f"Fehler beim Kopieren der Whitelist-Datei: {e}", style="bold red")

def deploy_api(server_name: str, options: List[str] = None):
    """
    Kopiert die ASA API ZIP-Datei in den Win64 Ordner vom Server.
    Der Dateiname wird aus den Optionen übernommen.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: @{server_name}", style="bold red")
        return

    if not server_id.startswith("asa-server-"):
        console.print(f"Ungültige Server-ID: {server_id}", style="bold red")
        return

    if not options or len(options) != 1:
        console.print("Fehler: Kein gültiger Dateiname für die API angegeben.", style="bold red")
        return

    api_filename = options[0]
    src_file = f"/home/ark/src/api/{api_filename}"
    container_file = f"/home/gameserver/server-files/ShooterGame/Binaries/Win64/{api_filename}"

    if not os.path.exists(src_file):
        console.print(f"Fehler: Lokale Datei {src_file} nicht gefunden.", style="bold red")
        return

    try:
        console.print(f"Kopiere {api_filename} nach {server_name}...", style="bold green")
        execute_command(["docker", "cp", src_file, f"{server_id}:{container_file}"])
        console.print(f"API-Datei {api_filename} erfolgreich kopiert.", style="bold green")
    except Exception as e:
        console.print(f"Fehler beim Kopieren der API-Datei: {e}", style="bold red")


# Kopiert die fehlende xaudio.dll in den Win64 Ordner vom Server
def deploy_xaudio(server_name: str):
    """
    Kopiert die fehlende xaudio.dll in den Win64 Ordner vom Server
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: @{server_name}", style="bold red")
        return

    if not server_id.startswith("asa-server-"):
        console.print(f"Ungültige Server-ID: {server_id}", style="bold red")
        return

    src_file = "/home/ark/src/xaudio/xaudio2_9.dll"
    container_file = "/home/gameserver/server-files/ShooterGame/Binaries/Win64/xaudio2_9.dll"

    if not os.path.exists(src_file):
        console.print(f"Fehler: Lokale Datei {src_file} nicht gefunden.", style="bold red")
        return

    try:
        console.print(f"Kopiere xaudio.dll nach {server_name}...", style="bold green")
        execute_command(["docker", "cp", src_file, f"{server_id}:{container_file}"])
        #log_message(server_name, "xaudio.dll erfolgreich kopiert.")
    except Exception as e:
        console.print(f"Fehler beim Kopieren der xaudio.dll: {e}", style="bold red")

# Kopiert die INI-Dateien (default) und optional auch allfällige definierte Plugin-Configurationen
def deploy_config(server_name: str, options: List[str] = None):
    """
    Kopiert Konfigurationsdateien für einen einzelnen Server.
    Fügt außerdem Inhalte von Dateien ein, wenn die Syntax ;<include:filename.ini> verwendet wird
    (nur für INI-Dateien). Plugins bleiben unberührt.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: @{server_name}", style="bold red")
        return

    if not server_id.startswith("asa-server-"):
        console.print(f"Ungültige Server-ID: {server_id}", style="bold red")
        return

    # Prüfung, ob der Server gestoppt werden muss
    if "--plugin" in options and len(options) == 1:
        console.print(f"Info: Server {server_name} ({server_id}) wird nicht gestoppt, da nur Plugins aktualisiert werden.", style="dim")
    else:
        # Server stoppen
        stop_server(server_id)
        # Überprüfen, ob der Server tatsächlich gestoppt ist
        time.sleep(1)
        result = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
        if result.returncode != 0 or result.stdout.strip() == "true":
            console.print(f"Fehler: Server {server_name} ({server_id}) konnte nicht gestoppt werden.", style="bold red")
            return

    # Konfigurationsdateien definieren
    config_files = {
        "GameUserSettings": {
            "local_path": f"/home/ark/etc/GameUserSettings-{server_name}.ini",
            "container_path": f"/home/gameserver/server-files/ShooterGame/Saved/Config/WindowsServer/GameUserSettings.ini",
            "use_extend": True,
            "type": "ini",
        },
        "Game": {
            "local_path": f"/home/ark/etc/Game-{server_name}.ini",
            "container_path": f"/home/gameserver/server-files/ShooterGame/Saved/Config/WindowsServer/Game.ini",
            "use_extend": True,
            "type": "ini",
        },
        "LethalProtection": {
            "local_path": f"/home/ark/etc/LethalProtection-{server_name}.json",
            "container_path": f"/home/gameserver/server-files/ShooterGame/Binaries/Win64/ArkApi/Plugins/LethalProtection/config.json",
            "use_extend": False,
            "type": "plugin",
        },
    }

    # Filtere basierend auf Optionen
    types_to_copy = set()
    if options:
        if "--plugin" in options:
            types_to_copy.add("plugin")
        if "--ini" in options:
            types_to_copy.add("ini")
    else:
        # Standard: Alles kopieren
        types_to_copy = {"ini"}

    # Debug: Logge die ausgewählten Typen
    console.print(f"Ausgewählte Typen für das Kopieren: {types_to_copy}", style="bold blue")

    for file_key, paths in config_files.items():
        # Überspringe Dateien, die nicht dem ausgewählten Typ entsprechen
        if paths["type"] not in types_to_copy:
            console.print(f"Überspringe {file_key}, da Typ '{paths['type']}' nicht ausgewählt ist.", style="dim")
            continue

        local_path = paths["local_path"]
        container_path = paths["container_path"]
        use_extend = paths["use_extend"]

        if os.path.exists(local_path):
            temp_path = f"{local_path}.tmp"
            try:
                with open(local_path, "r") as infile, open(temp_path, "w", newline="\r\n") as outfile:
                    for line in infile:
                        # Bei INI-Dateien die ;<include:...>-Syntax verarbeiten
                        if use_extend and line.strip().startswith(";<include:") and line.strip().endswith(">"):
                            extend_filename = line.strip()[10:-1]  # Extrahiere Dateinamen
                            extend_path = os.path.join(os.path.dirname(local_path), extend_filename)
                            if os.path.exists(extend_path):
                                console.print(f"Füge Datei {extend_filename} in {file_key} ein...", style="bold green")
                                with open(extend_path, "r") as extend_file:
                                    outfile.writelines(extend_file.readlines())
                            else:
                                console.print(f"Warnung: Datei {extend_filename} nicht gefunden!", style="bold yellow")
                        else:
                            # Normale Zeilen kopieren (Kommentare ignorieren)
                            if not line.lstrip().startswith(";"):
                                outfile.write(line)

                # Validierung der INI-Datei vor dem Kopieren
                validate_ini_file(temp_path, file_key)

                # Kopiere die temporäre Datei in den Container
                console.print(f"Kopiere {temp_path} nach {container_path}...")
                execute_command(["docker", "cp", temp_path, f"{server_id}:{container_path}"])
                log_message(server_name, f"{file_key} erfolgreich kopiert.")
            except Exception as e:
                console.print(f"Fehler beim Verarbeiten von {local_path}:\n{str(e)}", style="bold red")
                console.print(f"[bold red]Skript wird abgebrochen![/bold red]")
                sys.exit(1)
            finally:
                if os.path.exists(temp_path):
                    os.remove(temp_path)
        else:
            console.print(f"Warnung: Lokale Datei {local_path} nicht gefunden!", style="bold yellow")

def backup(server_name: str, sync_only: bool = False):
    """
    Erstellt ein Backup der Spieldaten eines Servers.
    Falls `sync_only` True ist, werden nur Dateien aus `map_sync` kopiert.
    Falls `sync_only` False ist, wird der gesamte Ordner kopiert.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: {server_name}", style="bold red")
        return

    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    backup_dir = f"/home/ark/backup/{server_name}/"
    tar_backup_file = f"/home/ark/backup/maps/{server_name}_{timestamp}.tar.gz"
    base_path = "/home/gameserver/server-files/ShooterGame/Saved/SavedArks/"
    config_files_path = "/home/gameserver/server-files/ShooterGame/Saved/Config/WindowsServer"

    if sync_only:
        os.makedirs(backup_dir, exist_ok=True)  # Beim Sync nicht löschen
    else:
        if os.path.exists(backup_dir):
            shutil.rmtree(backup_dir)  # Löscht den Ordner für normales Backup
        os.makedirs(backup_dir, exist_ok=True)

    try:
        # Unterordner in /SavedArks ermitteln
        console.print("")
        result = execute_command_with_output(["docker", "exec", server_id, "ls", "-1", base_path])
        if result.returncode != 0:
            console.print(f"Fehler beim Abrufen der Unterordner in {base_path} für {server_name}", style="bold red")
            return

        subfolders = result.stdout.splitlines()
        if not subfolders:
            console.print(f"Kein Unterordner in {base_path} gefunden!", style="bold red")
            return

        save_folder = None
        full_path = None
        
        # Copy Config
        execute_command(["docker", "cp", f"{server_id}:{config_files_path}/Game.ini", f"{backup_dir}/Game.ini"])
        execute_command(["docker", "cp", f"{server_id}:{config_files_path}/GameUserSettings.ini", f"{backup_dir}/GameUserSettings.ini"])

        # Suche den passenden Unterordner mit relevanten Dateien
        for folder in subfolders:
            folder_path = f"{base_path}{folder}/"

            # Prüfe, ob dieser Ordner Dateien enthält, die in map_sync gelistet sind
            console.print("Verfügbare Dateien:")
            result = execute_command_with_output(["docker", "exec", server_id, "ls", "-1", folder_path])
            if result.returncode != 0:
                continue  # Falls ein Fehler auftritt, diesen Ordner überspringen

            files = result.stdout.splitlines()
            files_to_copy = [file for file in files for pattern in map_sync if file.endswith(pattern[1:]) or file == pattern]

            if files_to_copy:
                save_folder = folder  # Setze den korrekten Map-Unterordner
                full_path = folder_path
                break  # Beende die Suche, sobald ein passender Ordner gefunden wurde

        if not save_folder or not full_path:
            console.print(f"Keine relevanten Dateien in {base_path} gefunden.", style="bold red")
            return

        if sync_only:
            # Erstelle das Backup-Verzeichnis mit Unterordner für die Map
            sync_backup_dir = os.path.join(backup_dir, save_folder)
            os.makedirs(sync_backup_dir, exist_ok=True)

            console.print(f"[{server_name}] Kopiere {len(files_to_copy)} Dateien...")
            

            for file in files_to_copy:
                execute_command(["docker", "cp", f"{server_id}:{full_path}{file}", f"{sync_backup_dir}/{file}"])
                console.print(f"[{server_name}] - {file}", style="bold green")

        else:
            # **Ohne `--sync`: GANZEN UNTERORDNER KOPIEREN**
            full_backup_dir = os.path.join(backup_dir, save_folder)
            log_message(server_name, "Vollständiges Backup: Kopiere gesamten Ordner...")

            execute_command(["docker", "cp", f"{server_id}:{full_path}", full_backup_dir])

            log_message(server_name, "Erstelle tar.gz Archiv...")
            subprocess.run(["tar", "czf", tar_backup_file, "-C", full_backup_dir, "."], check=True)

            backup_size = os.path.getsize(tar_backup_file) / (1024 * 1024)
            console.print(f"[{server_name}] Backup erstellt: {tar_backup_file} ({backup_size:.2f} MB)", style="bold green")
            log_message(server_id, "Backup erstellt")

    except Exception as e:
        console.print(f"Fehler beim Backup von {server_name}: {str(e)}", style="bold red")

# Spezielles Backup für Datenbank und Config, weil dieses nur 1x für alle Server ausgeführt werden muss
def backupdb():
    """
    Erstellt ein Backup aller MariaDB-Datenbanken im Container 'mariadb'.
    """
    # Einstellungen
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    mariadb_container = "mariadb"
    backup_dir = "/home/ark/backup/mariadb/"
    mariadb_backup_file = f"{backup_dir}mariadb_{timestamp}.sql"
    mariadb_tar_file = f"{backup_dir}mariadb_{timestamp}.tar.gz"
    tar_config_file = f"/home/ark/backup/config/config_{timestamp}.tar.gz"

    try:
        # Config
        console.print(f"Config-Backup wird erstellt...", style="bold green")
        subprocess.run([
            "tar", "czf", tar_config_file,
            "-C", "/home/ark", "etc",
            "-C", "/home/ark", "docker",
            "-C", "/home/ark", "bin",
            "-C", "/home/ark/share/CrossArkChat", "Config",
            "-C", "/var/www/ark/data", "asa"
        ], check=True)
    except Exception as e:
        console.print("Ein unerwarteter Fehler beim Config-Backup ist aufgetreten.", style="bold red")

    if MARIADB:
        try:
            # MariaDB
            console.print("Erstelle MariaDB-Backup...", style="bold green")
            with open(mariadb_backup_file, "w") as backup_file:
                result = subprocess.run([
                    "docker", "exec", mariadb_container, "mariadb-dump",
                    "-u", "root", f"-p{os.environ.get('MYSQL_ROOT_PASSWORD', 'XXXXX')}",
                    "--all-databases"
                ], stdout=backup_file, stderr=subprocess.PIPE, text=True)

            if result.returncode == 0:
                # Komprimiere das MariaDB-Backup
                subprocess.run([
                    "tar", "czf", mariadb_tar_file, "-C", backup_dir, f"mariadb_{timestamp}.sql"
                ], check=True)

                # Entferne das temporäre SQL-Backup
                os.remove(mariadb_backup_file)
                console.print(f"MariaDB-Backup erfolgreich: {mariadb_tar_file}", style="bold green")
            else:
                console.print(f"Fehler beim MariaDB-Backup: {result.stderr}", style="bold red")

        except Exception as e:
            console.print("Ein unerwarteter Fehler bei MariaDB-Backup ist aufgetreten.", style="bold red")
    else:
        console.print(f"MariaDB-Backup ist deaktiviert.", style="cyan")

# Simple Traid Konfiguration verteilt (von Island aus)
def deploy_shop(server_name: str, options: List[str] = None):
    """
    Simple Trade verteilen/holen.

    Regeln:
      --get        → wenn laufend: saveworld, dann 10s warten; wenn nicht laufend: nur 10s warten; dann aus Container ziehen.
      --settings   → falls läuft: stoppen, dann in Container kopieren.
      --packages   → falls läuft: stoppen, dann in Container kopieren.
      --validdata  → falls läuft: stoppen, dann in Container kopieren.
      --validates  → Alias für --validdata.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"Unbekannter Server: @{server_name}", style="bold red")
        return
    if not server_id.startswith("asa-server-"):
        console.print(f"Ungültige Server-ID: {server_id}", style="bold red")
        return
    if not options or len(options) != 1:
        help(); sys.exit(1)

    opt = options[0]
    if opt == "--validates":
        opt = "--validdata"

    # Pfade
    src_settings  = "/home/ark/etc/Simple_Trade-Settings.sav"
    src_packages  = "/home/ark/etc/Simple_Trade-PresetMarkets.sav"
    src_validdata = "/home/ark/etc/Simple_Trade-ValidData.sav"

    dst_settings  = "/home/gameserver/server-files/ShooterGame/Saved/SaveGames/Simple_Trade/Simple_Trade-Settings.sav"
    dst_packages  = "/home/gameserver/server-files/ShooterGame/Saved/SaveGames/Simple_Trade/Simple_Trade-PresetMarkets.sav"
    dst_validdata = "/home/gameserver/server-files/ShooterGame/Saved/SaveGames/Simple_Trade/Simple_Trade-ValidData.sav"

    # Läuft der Container?
    insp = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
    is_running = (insp.returncode == 0 and insp.stdout.strip() == "true")

    if opt == "--get":
        # Nur saveworld, wenn laufend; 10s warten in jedem Fall
        if is_running:
            try:
                saveworld(server_id)
                time.sleep(10)
            except Exception as e:
                log_message(server_name, f"saveworld fehlgeschlagen: {e}")
        try:
            console.print(f"Sichere Shop von {server_name}...", style="bold green")
            execute_command(["docker", "cp", f"{server_id}:{dst_settings}",  src_settings])
            execute_command(["docker", "cp", f"{server_id}:{dst_packages}",  src_packages])
            execute_command(["docker", "cp", f"{server_id}:{dst_validdata}", src_validdata])
            log_message(server_name, "Shop wurden erfolgreich gesichert.")
        except Exception as e:
            console.print(f"Fehler beim Sichern der Shop: {e}", style="bold red")
        return

    if opt in ("--settings", "--packages", "--validdata"):
        # Falls laufend → sauber stoppen; falls schon gestoppt → weiter
        if is_running:
            stop_server(server_id)
            time.sleep(1)
            insp2 = execute_command(["docker", "inspect", "-f", "{{.State.Running}}", server_id])
            if insp2.returncode != 0 or insp2.stdout.strip() == "true":
                console.print(f"Fehler: Server {server_name} ({server_id}) konnte nicht gestoppt werden.", style="bold red")
                return

        mapping = {
            "--settings":  (src_settings,  dst_settings,  "Settings"),
            "--packages":  (src_packages,  dst_packages,  "Packages"),
            "--validdata": (src_validdata, dst_validdata, "ValidData"),
        }
        src, dst, label = mapping[opt]

        if not os.path.exists(src):
            console.print(f"Fehler: Lokale {src} nicht gefunden.", style="bold red")
            return

        try:
            console.print(f"Kopiere Shop {label} nach {server_name}...", style="bold green")
            execute_command(["docker", "cp", src, f"{server_id}:{dst}"])
            log_message(server_name, f"Shop {label} wurden erfolgreich kopiert.")
        except Exception as e:
            console.print(f"Fehler beim Kopieren der Shop {label}: {e}", style="bold red")
        return

    help(); sys.exit(1)


def event_status(server_name: str):
    """
    Prüft, ob ein Event (Mod-ID aus `events`) auf dem Server aktiv ist.
    Gibt Eventnamen oder 'Kein Event aktiv' aus.
    """
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"[bold red]Unbekannter Server: @{server_name}[/bold red]")
        return

    try:
        with open(COMPOSE_FILE, "r", encoding="utf-8") as f:
            content = f.read()

        match = re.search(rf"{server_id}:[\s\S]*?-mods=([^\s]+)", content)
        if not match:
            console.print(f"{server_name} ({server_id}): [bold red]Keine Mod-Liste gefunden[/bold red]")
            return

        active_mods = match.group(1).split(',')
        active_event = next((name for name, e in events.items() if e["id"] in active_mods), None)

        if active_event:
            console.print(f"{server_name} ({server_id}): [bold green]{active_event}[/bold green]")
        else:
            console.print(f"{server_name} ({server_id}): [bold yellow]Kein Event[/bold yellow]")

    except Exception as e:
        console.print(f"[bold red]Fehler beim Statuslesen: {e}[/bold red]")

def deploy_event(server_name: str, options: List[str] = None):
    """
    Aktiviert oder deaktiviert Events in der docker-compose.yml,
    indem die Mod-ID in der ASA_START_PARAMS-Zeile hinzugefügt oder entfernt wird.
    """
    def load_compose_file() -> str:
        with open(COMPOSE_FILE, "r", encoding="utf-8") as f:
            return f.read()

    def write_compose_file(content: str):
        with open(COMPOSE_FILE, "w", encoding="utf-8") as f:
            f.write(content)

    def pick_event(opt: str, current_event_id: str = None) -> str:
        now = datetime.now()
        if opt == "--random":
            no_event_chance = 0.25  # 25% Chance für „kein Event“
            if random.random() < no_event_chance:
                return None
            available = [name for name, e in events.items() if e["id"] != current_event_id]
            return random.choice(available) if available else None
        elif opt == "--regular":
            for name, data in events.items():
                if "start" in data and "end" in data:
                    start = datetime.strptime(data["start"] + f".{now.year}", "%d.%m.%Y")
                    end = datetime.strptime(data["end"] + f".{now.year}", "%d.%m.%Y")
                    if start <= now <= end:
                        return name
        else:
            for name in events:
                if name.lower() == opt.replace("--", "").lower():
                    return name
        return None

    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"[bold red]Unbekannter Server: @{server_name}[/bold red]")
        return

    if not options or len(options) != 1:
        console.print("[bold red]Ein Event muss angegeben werden (z. B. --random, --regular, --TurkeyTrial oder --disable).[/bold red]")
        return

    disable_mode = options[0] == "--disable"
    selected_option = options[0]

    content = load_compose_file()

    # Suche ASA_START_PARAMS innerhalb environment
    pattern = rf"({server_id}:[\s\S]*?environment:\s*- ASA_START_PARAMS=)([^\n]+)"
    match = re.search(pattern, content)
    if not match:
        console.print(f"[bold red]ASA_START_PARAMS für {server_id} nicht gefunden.[/bold red]")
        return

    line_start = match.group(1)
    asa_params = match.group(2)

    # Aktuelle Mods extrahieren
    current_mods_match = re.search(r"-mods=([^\s]+)", asa_params)
    current_mods = current_mods_match.group(1).split(",") if current_mods_match else []

    known_event_ids = [e["id"] for e in events.values()]
    active_event_id = next((e["id"] for e in events.values() if e["id"] in current_mods), None)

    if disable_mode:
        console.print(f"[bold yellow]Deaktiviere Event-Mods auf {server_name}[/bold yellow]")
        new_mods = [mod for mod in current_mods if mod not in known_event_ids]
        if new_mods:
            new_asa_params = re.sub(r"-mods=[^\s]+", f"-mods={','.join(new_mods)}", asa_params) if "-mods=" in asa_params else f"{asa_params} -mods={','.join(new_mods)}"
        else:
            new_asa_params = re.sub(r"-mods=[^\s]+", "", asa_params).strip()
    else:
        event_name = pick_event(selected_option, active_event_id)

        if not event_name:
            console.print(f"[bold yellow]Kein Event ausgewählt für {server_name}[/bold yellow]")
            new_mods = [mod for mod in current_mods if mod not in known_event_ids]
            new_asa_params = re.sub(r"-mods=[^\s]+", f"-mods={','.join(new_mods)}", asa_params) if new_mods else re.sub(r"-mods=[^\s]+", "", asa_params).strip()
        else:
            event_id = events[event_name]["id"]
            
            if active_event_id and active_event_id != event_id:
                old_event_name = next((k for k,v in events.items() if v['id'] == active_event_id), None)
                if old_event_name:
                    console.print(f"[bold yellow]Vorher aktiv: {old_event_name} ({active_event_id})[/bold yellow]")
            
            removed_events = [
                name for name, e in events.items()
                if e["id"] in current_mods and e["id"] != event_id
            ]
            new_mods = [
                mod for mod in current_mods
                if mod not in known_event_ids or mod == event_id
            ]
            for ev in removed_events:
                ev_id = events[ev]["id"]
                console.print(f"[bold yellow]Entferne vorherigen Event: {ev} ({ev_id})[/bold yellow]")

            if event_id not in new_mods:
                new_mods.append(event_id)

            console.print(f"[bold green]Aktiviere Event: {event_name} ({event_id}) auf {server_name}[/bold green]")

            if "-mods=" in asa_params:
                new_asa_params = re.sub(r"-mods=[^\s]+", f"-mods={','.join(new_mods)}", asa_params)
            else:
                new_asa_params = f"{asa_params} -mods={','.join(new_mods)}"

    updated_content = content.replace(f"{line_start}{asa_params}", f"{line_start}{new_asa_params}")
    write_compose_file(updated_content)

    if disable_mode:
        log_message(server_id, "Alle Events wurden deaktiviert")
        console.print(f"[bold green]Event-Mods wurden entfernt.[/bold green]")
    elif not event_name:
        log_message(server_id, "Kein Event gesetzt (random none)")
        console.print(f"[bold cyan]Keine Event-Mod aktiv gesetzt.[/bold cyan]")
    else:
        log_message(server_id, f"Event {event_name} wurde aktiviert")
        console.print(f"[bold green]Event-Mod '{events[event_name]['id']}' erfolgreich gesetzt.[/bold green]")

    console.print(f"[bold blue]Starte Redeploy für {server_name}...[/bold blue]")
    result = execute_command(["/home/ark/bin/docker-deploy.bash", server_name])
    if result.returncode == 0:
        console.print(f"[bold green]{server_name} erfolgreich neu gestartet.[/bold green]")
    else:
        console.print(f"[bold red]Fehler beim Redeploy von {server_name}:[/bold red] {result.stderr.strip()}")

def get_current_map(compose_file: str) -> str:
    """
    Liest die aktuelle Karte aus der docker-compose.yml für asa-server-5.
    """
    try:
        with open(compose_file, 'r', encoding='utf-8') as file:
            content = file.read()

        server_block = re.search(r'asa-server-5:(.*?)ASA_START_PARAMS=([^\s]+)', content, re.DOTALL)
        if not server_block:
            raise ValueError("ASA_START_PARAMS für asa-server-5 nicht gefunden.")

        current_map = server_block.group(2).split('?')[0]
        return current_map
    except Exception as e:
        console.print(f"[bold red]Fehler beim Auslesen der aktuellen Karte: {e}[/bold red]")
        sys.exit(1)

def set_new_map(compose_file: str, old_map: str, new_map: str, new_mod_id: str = None):
    """
    Ersetzt die Karte und Mod-ID in der docker-compose.yml für asa-server-5.
    """
    try:
        with open(compose_file, 'r', encoding='utf-8') as file:
            content = file.read()

        updated_content = re.sub(
            rf'(asa-server-5:.*?ASA_START_PARAMS=){old_map}(?=\?)',
            rf'\1{new_map}',
            content,
            flags=re.DOTALL
        )

        old_mod_id = mod_map.get([k for k, v in mod_map.items() if v["id"] == old_map][0])["mod"]

        def update_mods(match):
            mods_list = match.group(2).split(',')
            if old_mod_id in mods_list:
                mods_list.remove(old_mod_id)
            if new_mod_id:
                mods_list.insert(0, new_mod_id)
            else:
                mods_list = [mod for mod in mods_list if mod != old_mod_id]
            return f"{match.group(1)}{','.join(mods_list).strip(',')}"

        updated_content = re.sub(
            r'(asa-server-5:.*?-mods=)([^\s]+)',
            update_mods,
            updated_content,
            flags=re.DOTALL
        )

        with open(compose_file, 'w', encoding='utf-8') as file:
            file.write(updated_content)

        console.print(f"[bold green]Karte erfolgreich auf {new_map} geändert.[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Fehler beim Ändern der Karte: {e}[/bold red]")
        sys.exit(1)

def rotationmap(target_name=None):
    """
    Rotation des 'rotation'-Servers mit Smooth Weighted Round-Robin.
    - Aktuelle Map wird ausgeschlossen.
    - k-Back verhindert unmittelbare Wiederholung.
    - Neue Maps/Gewichte werden automatisch berücksichtigt, weil Gewichte dynamisch aus mod_map gelesen werden.
    - State wird in WRR_STATE_FILE persistiert.
    """
    compose_file = COMPOSE_FILE

    # Ankündigung + sauberer Stop
    send_server_message("asa-server-5", "Server wechselt in Kürze die Karte!")
    stop_server("asa-server-5")
    deploy_config("rotation", [])

    current_map = get_current_map(compose_file)
    console.print(f"[bold yellow]Aktuelle Karte: {current_map}[/bold yellow]")

    if target_name:
        if target_name not in mod_map:
            console.print(f"[bold red]Ungültige Karte: {target_name}[/bold red]")
            sys.exit(1)
        new_key = target_name
    else:
        # SWRR-Auswahl
        new_key = _pick_next_map_swr(current_map)

    new_map_id = mod_map[new_key]["id"]
    new_mod_id = mod_map[new_key]["mod"]
    console.print(f"[bold green]Neue Karte: {new_map_id}[/bold green]")

    set_new_map(compose_file, current_map, new_map_id, new_mod_id)

    try:
        execute_command(["docker", "compose", "-f", compose_file, "--profile", "rotation", "down"])
        console.print("[bold blue]Docker Compose: Server heruntergefahren.[/bold blue]")
        execute_command(["docker", "compose", "-f", compose_file, "--profile", "rotation", "up", "-d"])
        console.print("[bold blue]Docker Compose: Server gestartet.[/bold blue]")
    except Exception as e:
        console.print(f"[bold red]Fehler beim Neustart des Servers: {e}[/bold red]")
        sys.exit(1)


def dynamicconfig(server_name: str, options: List[str] = None):
    server_id = servers.get(server_name)
    if not server_id:
        console.print(f"[bold red]Unbekannter Server: @{server_name}[/bold red]")
        return

    preset = "standard"
    if options:
        for opt in options:
            if opt == "--boosted":
                preset = "boosted"
            elif opt == "--standard":
                preset = "standard"

    config_values = DYNAMICCONFIG_PRESETS.get(preset)
    if not config_values:
        console.print(f"[bold red]Ungültiges Preset: {preset}[/bold red]")
        return

    config_path = f"/var/www/ark/data/asa/dynamicconfig_{server_name}.ini"
    # Datei schreiben
    try:
        with open(config_path, "w", encoding="utf-8") as f:
            for key, value in config_values.items():
                f.write(f"{key}={value}\n")

        log_message(server_name, f"dynamicconfig '{preset}' aktiviert")
        console.print(f"[bold green]{server_name} ({server_id}): dynamicconfig → {preset} → {config_path}[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Fehler beim Schreiben von {config_path}: {e}[/bold red]")
        sys.exit(1)

# Auflistung aller Funktionen
def help():
    """
    Zeigt eine Hilfeseite mit allen verfügbaren Befehlen, Gruppen, Servern und Optionen.
    """
    console.print("\n[bold yellow]Nutzung:[/bold yellow]")
    console.print("  server.py <command> [<options>] @<server|group>\n")
    
    console.print("[bold yellow]Verfügbare Befehle:[/bold yellow]")
    console.print("  start          Startet den angegebenen Server oder die Server in einer Gruppe.")
    console.print("  stop           Stoppt den angegebenen Server oder die Server in einer Gruppe.")
    console.print("  restart        Startet den angegebenen Server oder die Server in einer Gruppe neu.\n")

    console.print("  api            Kopiert die neuste API ZIP-Datei in den Win64 Ordner")
    console.print("  banlist        Aktualisiert die Banlist-Datei mit Online- und lokalen Einträgen.")
    console.print("  backup         Erstellt ein Backup der Spieldaten eines Servers.")    
    console.print("  backupdb       Erstellt ein Backup der Config und der MariaDB-Datenbanken (nur mit @all).")
    console.print("  bash           Open an Bash Shell for the server")
    console.print("  cleanup        Führt Bereinigungsbefehle auf dem Server aus (z. B. zerstört wilde Kreaturen).")
    console.print("  deploy         Überträgt Konfigurationsdateien auf den Server.")
    console.print("  dynamicconfig  Passt die DynamicConfig an.")
    console.print("  event          Aktiviert einen Event auf einer Karte.")
    console.print("  eventstatus    Zeigt den aktuellen Event auf der Karte an.")
    console.print("  listplayers    Zeigt die verbundenen Spieler eines Servers.")
    console.print("  log            Zeigt die Protokolle eines Servers an.")
    console.print("  rcon           Sendet einen RCON-Befehl an einen Server. Beispiel: server.py rcon <befehl> @server")
    console.print("  rotationmap    Beendet alle Rotation Server und startet zufüllig einen neuen neu")
    console.print("  saveworld      Speichert die Welt auf dem Server.")
    console.print("  shop           Verteilt die Simple Traid Dateien von Island auf alle anderen Server:")
    console.print("  status         Zeigt den Status (läuft/gestoppt) eines Servers.")
    console.print("  whitelist      Kopiert die Whitelist-Datei auf den Server.")
    console.print("  xaudio         Kopiert die fehlende xaudio.dll in den Win64 Ordner")
    
    console.print("\n[bold yellow]restart/stop:[/bold yellow]")
    console.print("  --warn         Gestaffelte Warnungen 15m..0s vor Stop/Restart")
    
    console.print("\n[bold yellow]deploy:[/bold yellow]")
    console.print("  --plugin       Kopiert nur die Plugin-Konfigurationsdateien.")
    console.print("  --ini          Kopiert nur die INI-Konfigurationsdateien.")
    console.print("  (keine Option) Kopiert alle verfügbaren Konfigurationsdateien (Standard).")
    
    console.print("\n[bold yellow]rotationmap:[/bold yellow]")
    console.print("  @all           Zufällig neue Karte wird ausgewählt.")
    console.print("  @<mapname>     Es wird eine Karte gezielt ausgewählt z.B. @center.")
    
    console.print("\n[bold yellow]shop:[/bold yellow]")
    console.print("  --get          Holt die Konfigurationsdateien.")
    console.print("  --settings     Speichert die Settings-Konfigurationsdatei.")
    console.print("  --packages     Speichert die Packages-Konfigurationsdatei.")
    console.print("  --validdata    Speichert die Packages-Konfigurationsdatei.")
    console.print("                 (Abschliessend immer ein 'docker-asa-deploy, wegen Berechtigungen!'", style="red")
    
    console.print("\n[bold yellow]event:[/bold yellow]")
    console.print("  --[EventName]   Aktiviert einen spezifischen Event.")
    console.print("  --random        Zufälliger Event wird aktiviert.")
    console.print("  --regular       Event gem. Datum wird aktiviert.")
    
    console.print("\n[bold yellow]dynamicconfig:[/bold yellow]")
    console.print("  --standard       Setzt normale Werte für Breeding/XP usw.")
    console.print("  --boosted        Setzt schnellere Werte für Breeding usw.")

    console.print("\n[bold yellow]Verfügbare Server:[/bold yellow]")
    for server in servers.keys():
        console.print(f"  {server}")

    console.print("\n[bold yellow]Verfügbare Gruppen:[/bold yellow]")
    for group, group_servers in groups.items():
        console.print(f"  {group}: {', '.join(group_servers)}")
    
    console.print("\n[bold yellow]Rotation Maps:[/bold yellow]")
    console.print(', '.join(mod_map.keys()))    

    console.print("\n[bold yellow]Beispiele:[/bold yellow]")
    console.print("  server.py start @island")
    console.print("  server.py deploy --plugin @all")
    console.print("  server.py backup @island")
    console.print("  server.py backupdb @all")
    console.print("  server.py rcon destroywilddinos @island\n")

# MAIN
if __name__ == "__main__":
    if len(sys.argv) < 2:
        help()
        sys.exit(1)

    command = sys.argv[1].lower()

    # Überprüfen, ob der Befehl gültig ist
    if command not in COMMANDS:
        console.print(f"Unbekannter Befehl: {command}", style="bold red")
        help()
        sys.exit(1)

    command_config = COMMANDS[command]
    custom_arg = None
    options = []
    target = None

    # Extrahiere Ziel, Optionen und Argumente
    if command_config.get("requires_argument", False):
        if len(sys.argv) < 4:  # Mindestens Befehl, Ziel und ein zusätzliches Argument müssen vorhanden sein
            console.print(f"Fehler: Kein Argument für {command} angegeben.", style="bold red")
            help()
            sys.exit(1)
        custom_arg = sys.argv[2]
        target = sys.argv[3]
    else:
        # Optionen extrahieren
        options = [arg for arg in sys.argv[2:] if arg.startswith("--")]
        # Ziel extrahieren
        non_option_args = [arg for arg in sys.argv[2:] if not arg.startswith("--")]
        if non_option_args:
            target = non_option_args[0]

    # Prüfe das Ziel
    if not target or not target.startswith("@"):
        console.print("Ungültige Zielangabe. Verwenden Sie '@' für Gruppen oder Server.", style="bold red")
        help()
        sys.exit(1)

    target_name = target[1:]  # Entferne das '@'

    try:
        process_target(command, target_name, custom_arg, options)
    except ValueError as ve:
        console.print(f"Fehler bei den Argumenten: {ve}", style="bold red")
        help()
        sys.exit(1)
