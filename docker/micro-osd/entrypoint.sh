#!/bin/bash

set -e
set -x

cp -a /ceph_zlog_plugin/libcls_zlog.so* /usr/lib/rados-classes

./micro-osd.sh /micro-osd
