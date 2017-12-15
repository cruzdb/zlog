FROM ubuntu:14.04
MAINTAINER Noah Watkins <noahwatkins@gmail.com>

# if firefly, set --without-cls-zlog-bench configuration option on zlog.
# ENV CEPH_VERSION firefly
ENV CEPH_VERSION jewel

### base dependencies
RUN apt-get update && apt-get install -y git wget vim tmux \
  python-virtualenv build-essential libprotobuf-dev \
  protobuf-compiler libboost-dev libtool automake autoconf \
  pkg-config libboost-system-dev libboost-program-options-dev \
  default-jdk openssh-server

### cache ceph source and build deps
RUN mkdir /src
RUN git clone --recursive https://github.com/ceph/ceph.git /src/ceph
RUN cd /src/ceph && apt-get update && ./install-deps.sh

### setup password-less ssh to localhost
RUN sed -i 's/UsePAM yes/UsePAM no/g' /etc/ssh/sshd_config
RUN ssh-keygen -f $HOME/.ssh/id_rsa -t rsa -N '' && \
  cat ~/.ssh/id_rsa.pub >> ~/.ssh/authorized_keys && \
  chmod 600 ~/.ssh/authorized_keys
RUN echo 'Host *\n  StrictHostKeyChecking no' > ~/.ssh/config

### install ceph-deploy
RUN git clone https://github.com/ceph/ceph-deploy /src/ceph-deploy
RUN cd /src/ceph-deploy && ./bootstrap
RUN ln -s /src/ceph-deploy/ceph-deploy /usr/bin/ceph-deploy

### install ceph base and librados
RUN ceph-deploy install --release ${CEPH_VERSION} `hostname`
RUN ceph-deploy pkg --install librados-dev `hostname`

### fetch, build, and install cls_zlog bits
RUN cd /src/ceph && \
  git remote add noahdesu https://github.com/noahdesu/ceph.git && \
  git fetch noahdesu && \
  git checkout -b zlog_bench/jewel noahdesu/zlog_bench/jewel && \
  ./autogen.sh && \
  ./configure --prefix=/usr --with-librocksdb-static

RUN cd /src/ceph/src && \
  make libcls_zlog_bench.la libcls_zlog_bench_client.la && \
  cp .libs/libcls_zlog_bench.so /usr/lib/rados-classes/ && \
  cp .libs/libcls_zlog_bench_client.* /usr/lib/ && \
  cp cls/zlog_bench/cls_zlog_bench_client.h /usr/include/rados/

### fetch zlog and build
RUN git clone --branch=physical-design https://github.com/cruzdb/zlog.git /src/zlog

# for firefly
#RUN cd /src/zlog && ./makeconf.sh && ./configure --without-cls-zlog --without-cls-zlog-bench && make
# for jewel
RUN cd /src/zlog && ./makeconf.sh && ./configure --without-cls-zlog && make

ADD entrypoint.sh /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]
