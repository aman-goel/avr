#!/bin/bash
# Make sure we exit if there is a failure
# set -e

RETURN=1

TIMEOUT=300
if [[ -z "${ENVTIMEOUT}" ]]; then
	TIMEOUT=300
else
	TIMEOUT=$ENVTIMEOUT
fi

if [ $# -lt 2 ]
then
	echo "Usage: <file> <name> <optional-args>"
	exit 1
fi

FILE="$1"
shift
NAME="$1"
shift
args=$@

OUTPATH="output"
outFile="$OUTPATH/$NAME.out"
errFile="$OUTPATH/$NAME.err"

python3 avr.py --name $NAME $args $FILE

prFile="$OUTPATH/work_$NAME/result.pr"
if test -f "$prFile"; then
	result=$(cat $prFile)
	if [ "${result}" == "avr-h" ]; then
		echo "Property proved."
		RETURN=0
	elif [ "${result}" == "avr-v" ]; then
		echo "Property violated."
		RETURN=0
	elif [ "${result}" == "avr-f_to" ]; then
		echo "Timeout reached."
	elif [ "${result}" == "avr-f_mo" ]; then
		echo "Memout reached."
	else
		echo "Error occurred."
	fi
else
	echo "Error occurred."
fi

if [ "${RETURN}" == "0" ]; then
	echo -e "NO ERROR"
    exit 0
else
	echo -e "ERROR"
    exit 1
fi
