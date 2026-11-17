# Macaulay2 in a container, for machines without a system install.
#   docker build -t k3-twists-m2 .
#   docker run --rm -v "$PWD":/work -w /work k3-twists-m2 make test
FROM ubuntu:26.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
 && apt-get install -y --no-install-recommends macaulay2 make coreutils \
 && rm -rf /var/lib/apt/lists/*
RUN useradd -m m2user
USER m2user
