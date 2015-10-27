FROM ubuntu:14.04

MAINTAINER Noah Watkins <noahwatkins@gmail.com>

RUN apt-get update && apt-get install -y git wget

# install ceph master development branch
RUN wget -q -O- 'https://ceph.com/git/?p=ceph.git;a=blob_plain;f=keys/autobuild.asc' | sudo apt-key add -
RUN echo deb http://gitbuilder.ceph.com/ceph-deb-$(lsb_release -sc)-x86_64-basic/ref/master $(lsb_release -sc) main | sudo tee /etc/apt/sources.list.d/ceph.list
RUN apt-get update && apt-get install -y --force-yes ceph librados-dev

# install ceph build dependencies and build zlog ceph plugin bits
RUN mkdir /src && cd /src && \
  git clone --recursive https://github.com/noahdesu/ceph.git && \
  cd ceph && \
  git checkout -b cls_zlog origin/cls_zlog && \
  bash ./install-deps.sh && \
  ./autogen.sh && \
  ./configure && \
  cd src && \
  make libcls_zlog.la && \
  make libcls_zlog_client.la && \
  cp .libs/libcls_zlog.so* /usr/lib/rados-classes/ && \
  cp .libs/libcls_zlog_client.so* /usr/lib/ && \
  cp cls/zlog/cls_zlog_client.h /usr/include/rados/ && \
  cd .. && \
  make clean

# install zlog
RUN cd /src && \
  apt-get install -y libprotobuf-dev protobuf-compiler && \
  git clone https://github.com/noahdesu/zlog.git && \
  cd zlog && \
  autoreconf -ivf && \
  ./configure && \
  make

ADD micro-osd.sh /src/micro-osd.sh
ADD entrypoint.sh /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
