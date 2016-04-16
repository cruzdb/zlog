## install docker

```bash
install-docker.sh
```

## checkout zlog

```bash
git clone --branch=physical-design https://github.com/noahdesu/zlog.git
pushd zlog/docker/physical-design
docker build -t zlog-pd .
```

## spin up a single osd

```bash
single-node-ceph.sh --data-dev sdc [--journal-dev sdd] [--noop dev[--noop dev ...]]
```
