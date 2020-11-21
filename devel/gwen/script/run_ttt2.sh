#!/bin/bash

DIR=$(dirname $0)
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
#! /bin/sh

  $DIR/ttt2 -c $DIR/ttt2rat.conf -t -p -s AUTO "$PROBLEM" > "$aproveOutput"
aproveResult=$(head -1 $aproveOutput | egrep '^YES|^NO')

if [ -z "$aproveResult" ]
then
    echo "MAYBE"
elif [ -e "$DIR/ttt2" ]; then
    exec $DIR/ttt2 -e -cpf -s AUTO -c ttt2rat.conf "$PROBLEM" > "$cpfProof"
elif [ -e Makefile ]; then
   
echo "Type 'make help' to get compilation instructions."
else
  echo "Could not find $DIR/ttt2 and this does not look like a source archive."
  echo "Giving up."
fi

# clean up
rm "$aproveOutput"
rm "$aproveProof"
