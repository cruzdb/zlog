#!/bin/bash

if test -e build; then
    echo "build dir already exists; rm -rf build and re-run"
    exit 1
fi

git submodule update --init --recursive

mkdir build
cd build
cmake "$@" ..

echo done.
