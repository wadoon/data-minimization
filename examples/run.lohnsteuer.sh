#!/bin/bash -x

P=examples/lohnsteuer_int.c
C1=examples/lohnsteuer_int.1.yml
C2=examples/lohnsteuer_int.2.yml


function call() {
  m=$1
  c=$2
  shift 2
  /usr/bin/time -a -f "$1,$2,%E,%e,%S,%U,%P,%M,%t,%K,%D,%p,%X,%Z,%F,%R,%W,%c,%w" -o time.csv \
    ./exec $m $c $P $@
}

function full() {
  echo "START $1"
  # call execute $1

  # call extract-facts-fwd $1

  # call fact-consistency $1 --fact-names=AUTO_FACTS

  call facts-preciseness $1 --fact-names=AUTO_FACTS

  # call minimize-facts-core $1 --fact-names=AUTO_FACTS

  # call symbex $1 --fact-names=AUTO_FACTS

  echo "END $1"
}

full $C1
# full $C2
