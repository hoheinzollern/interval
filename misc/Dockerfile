# If you modify this file, make sure to update the BUILD_IMAGE variable in .gitlab-ci.yml.

FROM debian:buster-slim

USER root

# install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -yq && \
    apt-get upgrade -yq --with-new-pkgs --auto-remove && \
    apt-get install -yq --no-install-recommends autoconf build-essential ca-certificates git graphviz g++ libgmp-dev ocaml-nox unzip wget && \
    apt-get clean

RUN wget --quiet https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux -O /usr/local/bin/opam && \
    chmod a+x /usr/local/bin/opam

# create user
RUN adduser --disabled-password --gecos '' user
USER user
ENV HOME /home/user
WORKDIR /home/user

# install opam
ENV OPAM_PACKAGES="conf-autoconf conf-g++"
RUN opam init -y --no-setup -j4 --bare --disable-sandboxing && \
    opam switch create minimal ocaml-system && \
    opam switch create latest  ocaml-system && \
    opam repository add coq-released https://coq.inria.fr/opam/released --all-switches && \
    opam install -y --switch=minimal $OPAM_PACKAGES coq.8.8.2  coq-bignums.8.8.0  coq-flocq.3.1.0 coq-mathcomp-ssreflect.1.7.0  coq-coquelicot.3.0.3 && \
    opam install -y --switch=latest  $OPAM_PACKAGES coq.8.15.1 coq-bignums.8.15.0 coq-flocq.4.0.0 coq-mathcomp-ssreflect.1.14.0 coq-coquelicot.3.2.0 && \
    opam clean -a -c -r -s --logs
