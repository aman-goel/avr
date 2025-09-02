#!/bin/bash

# Check if the number of arguments is not equal to 2
if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <benchmark> <certificate.sat>"
  exit 1 # Exit with a non-zero status to indicate an error
fi

outRoot="/tmp"
avrPath=$(dirname "$0")
benchmarkFile=$1
witnessFile=$2
benchmarkFileName=$(basename "$benchmarkFile")
benchmarkName="${benchmarkFileName%.*}"
outFile="${outRoot}/${benchmarkName}.out"
errFile="${outRoot}/${benchmarkName}.err"

CMD="python3 ${avrPath}/avr_pr.py ${benchmarkFile} --witness-file ${witnessFile} --out ${outRoot} --name ${benchmarkName}"
echo "Running `$CMD`"
$CMD  > ${outFile} 2> ${errFile}
if grep -q "proof race finished with answer unsafe" ${outFile}; then
  echo "sat"
elif grep -q "proof race finished with answer safe" ${outFile}; then
  echo "unsat"
else
  echo "unknown"
fi

rm -rf ${outRoot}/pr_${benchmarkName}
