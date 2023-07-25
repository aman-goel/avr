FROM ubuntu:latest

RUN apt-get update && apt-get install -y git wget python3 python3-distutils sudo nano && sudo ln -s /usr/bin/python3 /usr/bin/python

WORKDIR /app

RUN git clone https://github.com/aman-goel/avr.git
WORKDIR /app/avr
RUN chmod +x build.sh && chmod +x deps/build_deps.sh ## run build.sh manually, as it requires some y-s

CMD ["bash"]

