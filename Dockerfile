FROM ubuntu:22.04

RUN apt update
ARG DEBIAN_FRONTEND=noninteractive
RUN apt install -y racket
RUN apt install -y git libgmp3-dev make gcc
RUN git clone https://github.com/idris-lang/Idris2 /opt/idris2

WORKDIR /opt/idris2

ENV IDRIS2_CG=racket
RUN make bootstrap-racket
RUN make install

ENTRYPOINT [ "/root/.idris2/bin/idris2" ]
CMD [ "-h" ]