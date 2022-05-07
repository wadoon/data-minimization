#!/bin/bash -x

BASE=love_tester
P=$BASE.c
C1=$BASE.1.yml
C2=$BASE.2.yml
C3=$BASE.3.yml
C4=$BASE.4.yml

function call() {
  m=$1
  c=$2
  shift 2
  /usr/bin/time -a -f "$m,$c,%E,%e,%S,%U,%P,%M,%t,%K,%D,%p,%X,%Z,%F,%R,%W,%c,%w" -o time.csv \
    python ../exec.py $m $c $P $@
}

function full() {
  echo "START $1"
  call execute $1

  # not working well, need to redefine condition for inserting concrete value against symbolic value
  # call extract-facts-fwd $1

  call fact-consistency $1 --fact-names=USER_FACTS_0 --fact-names=USER_FACTS_1
  call facts-preciseness $1 --fact-names=USER_FACTS_0 --fact-names=USER_FACTS_1
  call minimize-facts-core $1 --fact-names=USER_FACTS_0 --fact-names=USER_FACTS_1
  call symbex $1 --fact-names=USER_FACTS_0 --fact-names=USER_FACTS_1
  echo "END $1"
}

 full $C1
 full $C2

# facts are imprecise
full $C3

# facts are no precise
full $C4

