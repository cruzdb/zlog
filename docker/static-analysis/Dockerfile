FROM ubuntu:zesty

RUN apt-get update && apt-get install -y \
  cppcheck \
  curl \
  cmake \
  clang-4.0 \
  llvm-4.0-dev \
  build-essential \
  libncurses5-dev \
  clang-4.0-dev \
  libz-dev \
  libfindbin-libs-perl

RUN curl -sSL https://github.com/include-what-you-use/include-what-you-use/archive/clang_4.0.tar.gz -o /tmp/iwyu.tar.gz
RUN mkdir -p /usr/src \
  && tar -xzf /tmp/iwyu.tar.gz -C /usr/src \
  && rm /tmp/iwyu.tar.gz \
  && mv /usr/src/include-what-you-use-clang_4.0 /usr/src/iwyu \
  && mkdir /usr/src/iwyu/build \
  && ( \
    cd /usr/src/iwyu/build \
    && cmake -DIWYU_LLVM_ROOT_PATH=/usr/lib/llvm-4.0 .. \
    && make -j$(getconf _NPROCESSORS_ONLN) \
    && make install \
  )

ENV CC clang-4.0
ENV CXX clang++-4.0

VOLUME /src/zlog
VOLUME /results

WORKDIR /src/zlog

ADD entrypoint.sh /usr/bin/entrypoint.sh

ENTRYPOINT ["entrypoint.sh"]
