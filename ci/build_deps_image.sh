#!/bin/bash
set -e
set -x

this_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
proj_dir=${this_dir}/../

. ${this_dir}/common.sh

base_img=${1}

img_tag=$(build_deps_image_tag ${base_img})

if [[ "$(docker images -q ${img_tag} 2> /dev/null)" == "" ]]; then
  tmp_dir=$(mktemp -d)
  cid_file="${tmp_dir}/cid"

  docker run --cidfile=${cid_file} \
    -v ${proj_dir}:/src/zlog:z,ro -w /src/zlog ${base_img} \
    /bin/bash -c "./install-deps.sh"

  cid=$(cat ${cid_file})
  docker commit ${cid} ${img_tag}
  rm -rf ${tmp_dir}
fi
