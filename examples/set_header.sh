#!/bin/bash

dir="$1"
suffix=".v"
header="// Author: Aman Goel (amangoel@umich.edu), University of Michigan\n"

for filename in $dir/*/*.v; do
	echo -e "$header" | cat - $filename > temp && mv temp $filename
	echo "file: $filename"
done

