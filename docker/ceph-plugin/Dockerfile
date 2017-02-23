FROM ubuntu:xenial

RUN apt-get update && apt-get install -y \
        git ccache \
        libprotobuf-dev protobuf-compiler # for cls_zlog

ENV PATH "/usr/lib/ccache:$PATH"
RUN ccache -M 5G

RUN git clone --recursive https://github.com/noahdesu/ceph.git /ceph
RUN cd /ceph && ./install-deps.sh && ./do_cmake.sh && git clean -dxf

VOLUME ["/ceph_zlog_plugin"]

ADD entrypoint.sh /entrypoint.sh
ENTRYPOINT ["./entrypoint.sh"]
