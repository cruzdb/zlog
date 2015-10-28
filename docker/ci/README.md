zlog-ci
=======

This Dockerfile is used to create an image runs the zlog continuous
integration test suite.

Usage
-----

By default the image will checkout and build zlog from the master branch of
the repository located at https://github.com/noahdesu/zlog:

  `docker run zlog/ci`

Use `-e "branch=different-branch` to checkout a different branch:

  `docker run -e "branch=testing" zlog/ci`

A zlog source directory on the host can be used instead using a bind mount. In
this case the `branch` environment variable is ignored:

  `docker run -v /tmp/host_zlog:/src/zlog zlog/ci`
