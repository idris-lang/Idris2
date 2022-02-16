FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
RUN apt update && apt install -y gcc git make racket libgmp3-dev build-essential clang
RUN git clone https://github.com/idris-lang/Idris2 /opt/idris2

WORKDIR /opt/idris2

ENV IDRIS2_CG=racket
RUN make bootstrap-racket
RUN make install

RUN export PATH="${PATH}:/root/.idris2/bin"

ENTRYPOINT [ "idris2" ]
CMD [ "-h" ]