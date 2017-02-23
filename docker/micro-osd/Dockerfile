FROM ubuntu:xenial

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y wget \
        software-properties-common apt-transport-https

RUN wget -q -O- 'https://download.ceph.com/keys/release.asc' | apt-key add -
RUN apt-add-repository "deb https://download.ceph.com/debian-kraken/ xenial main"

RUN apt-get update && apt-get install -y ceph

VOLUME ["/cls_zlog_plugin"]
VOLUME ["/micro-osd"]

ADD micro-osd.sh /micro-osd.sh
ADD entrypoint.sh /entrypoint.sh

###
RUN apt-get install -y uuid-runtime
RUN apt-get install -y libprotobuf-dev

ENTRYPOINT ["./entrypoint.sh"]
