FROM ubuntu:14.04

MAINTAINER Noah Watkins <noahwatkins@gmail.com>

### base dependencies
RUN apt-get update && apt-get install -y git wget vim tmux \
  build-essential libprotobuf-dev protobuf-compiler libboost-dev \
  libtool automake autoconf pkg-config libboost-system-dev \
  libboost-program-options-dev default-jdk && \
  apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

### cache ceph source and install build deps
RUN mkdir /src
RUN git clone --recursive https://github.com/ceph/ceph.git /src/ceph
RUN cd /src/ceph && apt-get update && ./install-deps.sh && \
  apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

### install ceph and librados
RUN wget -q -O- 'https://download.ceph.com/keys/release.asc' | apt-key add -
RUN echo "deb http://download.ceph.com/debian-jewel/ trusty main" | tee /etc/apt/sources.list.d/ceph-jewel.list
RUN apt-get update && apt-get install -y --force-yes ceph librados-dev && \
  apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

### fetch, build, and install cls_zlog bits
RUN cd /src/ceph && \
  git remote add noahdesu https://github.com/noahdesu/ceph.git && \
  git fetch noahdesu && \
  git checkout -b zlog/jewel noahdesu/zlog/jewel && \
  ./autogen.sh && ./configure --prefix=/usr

RUN cd /src/ceph/src && \
  make libcls_zlog.la libcls_zlog_client.la && \
  cp .libs/libcls_zlog.so /usr/lib/rados-classes/ && \
  cp .libs/libcls_zlog_client.* /usr/lib/ && \
  cp cls/zlog/cls_zlog_client.h /usr/include/rados/

RUN git clone --recursive https://github.com/cruzdb/zlog.git /src/zlog
RUN cd /src/zlog && ./makeconf.sh && ./configure --prefix=/usr && make && make install

ADD entrypoint.sh /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]
