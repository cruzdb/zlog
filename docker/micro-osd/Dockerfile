FROM ubuntu:16.04

# keep in sync with the first layer of the micro-osd image
RUN DEBIAN_FRONTEND=noninteractive apt-get update && apt-get install -y wget && \
    wget -q -O- 'https://download.ceph.com/keys/release.asc' | apt-key add - && \
    echo "deb http://download.ceph.com/debian-luminous/ xenial main" | \
		tee /etc/apt/sources.list.d/ceph-luminous.list && \
    apt-get update && apt-get install -y --force-yes ceph-mon ceph-osd \
        libprotobuf9v5 uuid-runtime && \
    apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

VOLUME ["/ceph_plugin"]

WORKDIR /

ADD micro-osd.sh /
ADD entrypoint.sh /
ENTRYPOINT ["/entrypoint.sh"]
