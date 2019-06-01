#!/bin/bash
set -e
set -x

this_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
proj_dir=${this_dir}/../

. ${this_dir}/common.sh

base_img=${1}
img_tag=$(build_deps_image_tag ${base_img})

if [ "x${BUILD_PKG}" == "xyes" ]; then
  pkg_img_tag=$(build_pkg_deps_image_tag ${base_img})
  docker run --rm -v ${proj_dir}:/src/zlog:z,ro \
    -v ${pkg_img_tag}_vol:/zlog_build \
    -e BUILD_PKG \
    -w /src/zlog ${base_img} /bin/bash -c "pushd /zlog_build; dnf install -y *.rpm; popd; ci/test.sh"
else
  docker run --rm -v ${proj_dir}:/src/zlog:z,ro \
    -w /src/zlog ${img_tag} /bin/bash -c "ci/test.sh"
fi
