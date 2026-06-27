#!/bin/bash

# Pfad zur docker-compose.yml
COMPOSE_FILE="/home/ark/docker/asa/docker-compose.yml"

# Container aus docker-compose.yml extrahieren, nur asa-server-Container berücksichtigen
extract_containers() {
    grep '^[[:space:]]*asa-server-[0-9]*:' "$COMPOSE_FILE" | awk -F: '{print $1}' | xargs
}

# Container stoppen und neu starten
process_container() {
    local container=$1
    local profile=$2

    echo "Verarbeite Container: $container mit Profil: $profile"

    cd /home/ark/docker/asa || { echo "Fehler: Verzeichnis nicht gefunden."; exit 1; }

    if [ "$RESET_MODE" != true ]; then
        /home/ark/bin/server stop @$profile
    fi

    docker compose -f docker-compose.yml --profile $profile down $( [ "$RESET_MODE" == true ] && echo "--volumes" )
    docker compose -f docker-compose.yml --profile $profile up -d
    sleep 5s
    /home/ark/bin/server start @$profile
}

# Profile aus der docker-compose.yml extrahieren
extract_profiles() {
    grep 'profiles:' "$COMPOSE_FILE" | sed -e 's/.*profiles: \[//' -e 's/\].*//' | tr ',' '\n' | sed 's/ //g' | sort -u
}

# Profile anzeigen
show_profiles() {
    echo ""
    echo "Verfügbare Profile:"
    echo "$AVAILABLE_PROFILES"
    echo ""
    echo "Verwendung:"
    echo "$0 [--reset] <profilename | all>"
    echo "--reset: Löscht auch Volumes des Profils."
}

# Hauptlogik
RESET_MODE=false
AVAILABLE_PROFILES=$(extract_profiles)
[ -z "$AVAILABLE_PROFILES" ] && { echo "Keine Profile gefunden."; exit 1; }

if [ "$1" == "--reset" ]; then
    RESET_MODE=true
    SELECTED_PROFILE=$2
else
    SELECTED_PROFILE=$1
fi

[ -z "$SELECTED_PROFILE" ] && { show_profiles; exit 0; }

#if [ "$SELECTED_PROFILE" == "all" ]; then
#    for container in $(extract_containers); do
#        process_container "$container" "$container"
#    done
#    exit 0
#fi

if ! echo "$AVAILABLE_PROFILES" | grep -q "^$SELECTED_PROFILE$"; then
    echo "Ungültiges Profil: $SELECTED_PROFILE"
    show_profiles
    exit 1
fi

process_container "$SELECTED_PROFILE" "$SELECTED_PROFILE"
