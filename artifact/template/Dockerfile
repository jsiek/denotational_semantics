# The toolchain of the artifact: Agda 2.8.0 (the official static Linux
# binary) and the Agda standard library 2.4, both pinned by checksum.
# TypeTopology is vendored in vendor/TypeTopology/, so typechecking needs
# no network access.
#
#   docker build -t iswim-mu .
#   docker run --rm iswim-mu                 # make check check-scott tables
#   docker run --rm iswim-mu make tables     # or any one target

FROM ubuntu:24.04

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl xz-utils make python3 \
 && rm -rf /var/lib/apt/lists/*
ENV LANG=C.UTF-8 LC_ALL=C.UTF-8

ARG AGDA_URL=https://github.com/agda/agda/releases/download/v2.8.0/Agda-v2.8.0-linux.tar.xz
ARG AGDA_SHA256=824081b8dcbe431289a50ac6bd83e451f390c51c3884ac7a8c4a5c0df2632faf
ARG STDLIB_URL=https://github.com/agda/agda-stdlib/archive/refs/tags/v2.4.tar.gz
ARG STDLIB_SHA256=dd0fab4519523d6c08cd9583a4f5eac38ab135a12ccdab1fb164c271075f6747

RUN curl -fsSL -o /tmp/agda.tar.xz "$AGDA_URL" \
 && echo "$AGDA_SHA256  /tmp/agda.tar.xz" | sha256sum -c - \
 && tar -xJf /tmp/agda.tar.xz -C /usr/local/bin agda \
 && rm /tmp/agda.tar.xz \
 && curl -fsSL -o /tmp/stdlib.tar.gz "$STDLIB_URL" \
 && echo "$STDLIB_SHA256  /tmp/stdlib.tar.gz" | sha256sum -c - \
 && mkdir -p /opt \
 && tar -xzf /tmp/stdlib.tar.gz -C /opt \
 && rm /tmp/stdlib.tar.gz

# the libraries file of Agda: the standard library
ENV AGDA_DIR=/opt/agda
RUN mkdir -p "$AGDA_DIR" \
 && echo /opt/agda-stdlib-2.4/standard-library.agda-lib > "$AGDA_DIR/libraries" \
 && agda --version

WORKDIR /artifact
COPY . /artifact

CMD ["make", "all"]
