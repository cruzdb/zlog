## checkout zlog

```bash
git clone --branch=physical-design https://github.com/noahdesu/zlog.git
pushd zlog/docker/physical-design
```

## install docker and build zlog image

```bash
install-docker.sh
docker build -t zlog-pd .
```


## spin up a single osd

```bash
single-node-ceph.sh --data-dev sdc [--journal-dev sdd] [--noop dev[--noop dev ...]]
```

## pull zlog ceph deps out of image

```bash
docker run -v /usr/lib/rados-classes/:/deps -it zlog-pd --deps /deps/
sudo service ceph-osd-all restart
```
