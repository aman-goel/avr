#!/bin/bash

run_config () {
    while read -r id name args
    do
        [ -z "$id" ] && continue
        
        if [ $id = "#" ]
        then
            continue
        fi
        cmd="$id $name $args"
        echo -e "Running $cmd"
        $cmd
    done < $1
}

run_config "config.txt" &&
exit
 
