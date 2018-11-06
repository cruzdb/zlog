#!/bin/bash
set -e

this_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
proj_dir=${this_dir}/../

. ${this_dir}/common.sh

base_img=${1}
img_tag=$(build_deps_image_tag ${base_img})

docker run --rm -v ${proj_dir}:/src/zlog:z,ro \
  -w /src/zlog ${img_tag} /bin/bash -c "ci/test.sh"
