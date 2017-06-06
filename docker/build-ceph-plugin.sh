#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -i|--docker-image)
      docker_img="$2"
      shift
      ;;
    -c|--ceph-ver)
      ceph_ver="$2"
      shift
      ;;
    *)
      echo "unknown argument $key"
      exit 1
      ;;
  esac
  shift
done

function usage() {
  local name="$(basename $0)"
  echo "./$name -i|--docker-image <docker-img> -c|--ceph-ver <ceph-ver>"
  echo "example: ./$name -i centos:7 -c kraken"
}

if [ -z "$docker_img" ]; then
  usage
  exit 1 
fi
if [ -z "$ceph_ver" ]; then
  usage
  exit 1 
fi

configname="${docker_img}.${ceph_ver}"
dockerfile="Dockerfile.${configname}"
outputdir="libcls_zlog_${configname}"
if [ "x$ceph_ver" == "xluminous" ]; then 
  tdir=$(mktemp -d)
  trap "rm -rf $tdir" EXIT
  pushd ${THIS_DIR}/ceph-plugin/${ceph_ver}
  sed "s/%%DOCKER_IMAGE%%/${docker_img}/g" < Dockerfile.tmpl > $dockerfile
  docker build -t $configname -f $dockerfile .
  docker run --rm -v $tdir:/plugin-output $configname
  popd
  rm -rf $outputdir
  mv $tdir $outputdir
else
  echo "unsupported ceph version: $ceph_ver"
  echo "available versions: luminous"
  exit 1
fi
