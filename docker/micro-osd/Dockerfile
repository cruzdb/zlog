FROM ubuntu:xenial

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y wget \
        software-properties-common apt-transport-https \
        uuid-runtime libprotobuf9v5 libprotobuf-lite9v5 && \
        apt-get clean -y && \
        apt-get autoclean -y && \
        apt-get autoremove -y

RUN wget -q -O- 'https://download.ceph.com/keys/release.asc' | apt-key add -
RUN apt-add-repository "deb https://download.ceph.com/debian-kraken/ xenial main"

RUN apt-get update && apt-get install -y ceph && \
        apt-get clean -y && \
        apt-get autoclean -y && \
        apt-get autoremove -y

VOLUME ["/cls_zlog_plugin"]
VOLUME ["/micro-osd"]

ADD micro-osd.sh /micro-osd.sh
ADD entrypoint.sh /entrypoint.sh

ENTRYPOINT ["./entrypoint.sh"]
