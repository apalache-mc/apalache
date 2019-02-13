#!/bin/bash

set -e 

TIMEOUT=2h
TLC_HOME_FILE=tlchome.conf
timer="timeout $TIMEOUT /usr/bin/time --verbose"
APALACHE_DIR=$(dirname $(dirname "$(readlink -f "$0")"))    
CMD="$APALACHE_DIR/bin/apalache-mc check" 

if [ -f $TLC_HOME_FILE ]; then
  TLC_HOME=$(head -n 1 $TLC_HOME_FILE)
  # if [ -f $TLC_HOME ]; then
    FOLDER=$1
    FILE=$2

    if [ -f $FILE ] && [ -d $FOLDER ]; then
   
      echo "Testing $FILE"
      $timer -o $FOLDER/profile_apalache_$(basename $FILE).txt $CMD ${@:3} $FILE > $FOLDER/log_apalache_$(basename $FILE).txt
    
    else
      echo "$FILE or $FOLDER does not exist"
      exit 1
    fi
    # repeat for TLC
    # $timer $timerFlags -o $FOLDER/profile_$(basename $FILE).txt $CMD ${@:3} $FILE > $FOLDER/apalache_$(basename $FILE).txt
  # else
   # echo "TLC directory $TLC_HOME does not exist. Please run ./configTLChome.sh <TLC_DIR> again" 
   # exit 1
  # fi
else
   echo "TLC directory not configured. Please run ./configTLChome.sh <TLC_DIR>"
   exit 1
fi



