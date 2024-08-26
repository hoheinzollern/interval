# If you modify this file, make sure to update the BUILD_IMAGE variable in .gitlab-ci.yml.

FROM debian:bullseye-slim

USER root

# install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -yq && \
    apt-get upgrade -yq --with-new-pkgs --auto-remove && \
    apt-get install -yq --no-install-recommends autoconf build-essential ca-certificates git graphviz g++ libgmp-dev ocaml-nox opam pkg-config && \
    apt-get clean

# create user
RUN adduser --disabled-password --gecos '' user
USER user
ENV HOME /home/user
WORKDIR /home/user

# install opam
ENV OPAM_PACKAGES="conf-autoconf conf-g++"
RUN opam init -y --no-setup -j4 --bare --disable-sandboxing && \
    opam switch create minimal ocaml-system && \
    opam switch create full    ocaml-system && \
    opam switch create latest  ocaml-system && \
    opam repository add coq-released https://coq.inria.fr/opam/released --all-switches && \
    opam install -y --switch=minimal $OPAM_PACKAGES coq.8.13.2 coq-bignums.8.13.0        coq-flocq.3.2.1 coq-mathcomp-ssreflect.1.12.0 coq-coquelicot.3.1.0 && \
    opam install -y --switch=full    $OPAM_PACKAGES coq.8.16.1 coq-bignums.8.16.0        coq-flocq.4.1.4 coq-mathcomp-ssreflect.1.18.0 coq-coquelicot.3.3.1 && \
    opam install -y --switch=latest  $OPAM_PACKAGES coq.8.19.2 coq-bignums.9.0.0+coq8.19 coq-flocq.4.2.0 coq-mathcomp-ssreflect.2.2.0  coq-coquelicot.3.4.2 && \
    opam clean -a -c -r -s --logs
