FROM ubuntu:20.04

ENV TZ="America/Detroit"
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt-get update && apt-get install -y git wget python3 python3-distutils sudo nano && sudo ln -s /usr/bin/python3 /usr/bin/python

WORKDIR /app

RUN git clone https://github.com/aman-goel/avr.git
WORKDIR /app/avr
RUN sed -i 's/-n "$(uname -a | grep Ubuntu)"/1 -eq 1/g' build.sh ## to get rid of OS check
RUN chmod +x build.sh && chmod +x deps/build_deps.sh
RUN ./build.sh

CMD ["bash"]

