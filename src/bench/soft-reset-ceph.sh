#!/bin/bash

set -x
set -e

sudo stop ceph-all || true
sudo stop ceph-all || true

find /var/lib/ceph -mindepth 1 -maxdepth 2 -type d -exec umount {} \; || true

rm -rf /etc/ceph/*
rm -rf /var/log/ceph/*
rm -rf /var/lib/ceph/mon/*
rm -rf /var/lib/ceph/tmp/*
rm -rf /var/lib/ceph/osd/*
rm -rf /var/lib/ceph/bootstrap-osd/*
rm -rf /var/lib/ceph/radosgw/*
rm -rf /var/lib/ceph/mds/*
rm -rf /var/lib/ceph/bootstrap-mds/*
