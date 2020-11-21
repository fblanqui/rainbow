#!/bin/bash

PROBLEM="$1"
if [ $# = 2 ]; then
    TIMEOUT="$2"
else
    TIMEOUT=0
fi

aproveOutput=$(mktemp)
aproveProof=$(mktemp)
cpfProof=$(basename ${1%%.xml}).proof.xml


export PATH=./bin:$PATH

# do the proof

# manifest file with Main
java -jar aprove.jar -C rainbow -p xml -m wst -t 30 -s full.strategy "$PROBLEM"  > "$aproveOutput"

# Mainfest file with ceta
#java -ea -jar aprove.jar "$PROBLEM" "$TIMEOUT" color.strategy > "$aproveOutput"

# get result
aproveResult=$(head -1 $aproveOutput | egrep '^YES|^NO')

if [ -z "$aproveResult" ]
then
    echo "MAYBE"
else
    # save the proof
    tail -1 "$aproveOutput" > "$aproveProof"

    # convert from AProVE-XML to CPF
    #java -jar -Xmx2G saxon9.jar "$aproveProof" ./aproveToCPF2.xsl > "$cpfProof"
    java -jar saxon9.jar "$aproveProof" ./aproveToCPF2.xsl > "$cpfProof"

    # show Yes or No on stderr
    echo "$aproveResult"
fi

# clean up
rm "$aproveOutput"
rm "$aproveProof"
