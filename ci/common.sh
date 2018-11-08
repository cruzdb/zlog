#!/bin/bash
set -e

this_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
proj_dir=${this_dir}/../

function build_deps_image_tag() {
  local base_img=${1}
  local deps_md5=$(cat ${proj_dir}/install-deps.sh | md5sum | awk '{print $1}')
  local img_tag="${base_img//[:.]/_}_${deps_md5}"
  echo ${img_tag}
}
