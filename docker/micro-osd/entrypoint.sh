#!/bin/bash

set -e
set -x

cp -a /ceph_plugin/* /usr/lib/rados-classes/

/micro-osd.sh /micro-osd
