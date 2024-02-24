# Using docker for avr

0. have docker and docker-compose set up on your machine, create input_files directory in this folder
1. docker-compose up -d
2. docker exec -it docker-avr-1 bash
3. run ./build.sh manually, as it is interactive
4. use the examples in this repository or put any input files into the input_files directory besides the docker files, it will be available under /app/input_files
5. use avr
