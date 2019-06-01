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

# if we are going to build zlog packages, then we'll use the deps image created
# above as a base. note that this is currently specific to fedora. all this will
# probably need to be generalized/changed when considering other distributions.
if [ "x${BUILD_PKG}" == "xyes" ]; then
  pkg_img_tag=$(build_pkg_deps_image_tag ${base_img})
  if [[ "$(docker images -q ${pkg_img_tag} 2> /dev/null)" == "" ]]; then
    tmp_dir=$(mktemp -d)
    cid_file="${tmp_dir}/cid"

    docker volume create --name "${pkg_img_tag}_vol"

    docker run --cidfile=${cid_file} \
      -v ${pkg_img_tag}_vol:/tmp/zlog_build \
      -v ${proj_dir}:/src/zlog:z,ro \
      -w /src/zlog ${img_tag} \
      /bin/bash -c "./ci/build-pkg.sh"

    cid=$(cat ${cid_file})
    docker commit ${cid} ${pkg_img_tag}
    rm -rf ${tmp_dir}
  fi
fi
