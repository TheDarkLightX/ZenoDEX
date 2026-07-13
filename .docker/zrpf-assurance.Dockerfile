FROM ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
        build-essential \
        ca-certificates \
        git \
        libssl-dev \
        pkg-config \
        python3 \
    && rm -rf /var/lib/apt/lists/*

RUN groupadd --gid 10001 zrpf \
    && useradd --create-home --home-dir /home/zrpf --uid 10001 --gid 10001 zrpf

USER 10001:10001
WORKDIR /out
