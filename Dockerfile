FROM ubuntu:20.04 AS build

RUN apt update && apt install gcc make chezscheme -y

WORKDIR /opt/idris2

ADD Makefile .
ADD libs .
ADD src .
ADD support .

ADD Release/ Release/
ADD config.mk .
ADD idris2api.ipkg .
ADD support/ support/
ADD LICENSE .
ADD bootstrap/ bootstrap/
ADD libs/ libs/
ADD tests/ tests/
ADD Makefile .
ADD bootstrap-rkt.sh .
ADD README.md .
ADD bootstrap.sh .
ADD idris2.ipkg .
ADD src/ src/

ENV SCHEME=scheme

RUN make bootstrap-build

RUN make install

FROM ubuntu:20.04

RUN apt update && apt install make chezscheme -y

RUN mkdir -p /root/.idris2

COPY --from=build /root/.idris2 /root/.idris2

ENV PATH="/root/.idris2/bin:${PATH}"

