## checkout zlog

```bash
git clone --branch=physical-design https://github.com/noahdesu/zlog.git
pushd zlog/docker/physical-design
```

## install docker and build zlog image

```bash
./install-docker.sh

# logout/login. docker should be successfully installed:
./install-docker.sh 
Docker installed successfully

docker build -t zlog-pd .
```


## spin up a single osd

```bash
./single-node-ceph.sh --data-dev sdc [--journal-dev sdd] [--noop dev[--noop dev ...]]
```

For instance on Wisconsin Cloud Lab there is an SSD device available at `/dev/sdc` (verify with dmesg or your favorite way to inspect the system). This would support to a possible invocation of `single-node-ceph.sh`:

```bash
./single-node-ceph.sh --data-dev sdc --noop sdc
```

## pull zlog ceph deps out of image

```bash
docker run -v /usr/lib/rados-classes/:/deps -it zlog-pd --deps /deps/
sudo service ceph-osd-all restart
sudo service ceph-osd-all restart # run again if first time has a problem
```

## run the physical design experiment

Edit the parameters at the top of `run.sh` to configure the test.

```bash
./run.sh
```
