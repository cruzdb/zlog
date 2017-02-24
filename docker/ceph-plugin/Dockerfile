FROM ubuntu:xenial

RUN apt-get update && apt-get install -y \
        git \
        libprotobuf-dev protobuf-compiler && \
        apt-get clean -y

RUN git clone --recursive --branch zlog/master-pb https://github.com/noahdesu/ceph.git /ceph && \
        cd /ceph && \
        find ./ -name .git -execdir git gc --aggressive --prune ";" && \
        cd .. && tar czf ceph.tar.gz ceph && rm -rf ceph

VOLUME ["/ceph_zlog_plugin"]

ADD entrypoint.sh /entrypoint.sh
ENTRYPOINT ["./entrypoint.sh"]
