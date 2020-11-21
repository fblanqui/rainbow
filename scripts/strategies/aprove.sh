#!/bin/bash

PROBLEM="$1"
if [ $# = 2 ]; then
    TIMEOUT="$2"
else
    TIMEOUT=0
fi

cpfProof=$(basename ${1%%.xml}).xml

export PATH=./bin:$PATH

# do the proof

# manifest file with Main

java -jar aprove.jar -C rainbow -p cpf -t 60 -s basic_dpi.strategy "$PROBLEM" > "$cpfOutput"
