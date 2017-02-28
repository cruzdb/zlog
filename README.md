# Zlog - a distributed shared log for ceph

[![Build Status](https://travis-ci.org/noahdesu/zlog.svg?branch=master)](https://travis-ci.org/noahdesu/zlog)
[![Coverity Scan Build Status](https://scan.coverity.com/projects/9894/badge.svg)](https://scan.coverity.com/projects/noahdesu-zlog)
[![codecov](https://codecov.io/gh/noahdesu/zlog/branch/master/graph/badge.svg)](https://codecov.io/gh/noahdesu/zlog)
[![docs](https://img.shields.io/badge/docs-latest-brightgreen.svg?style=flat)](https://noahdesu.github.io/zlog)

Zlog is a strongly consistent shared log designed to run on top of Ceph.
Specifically, it is an implementation of the CORFU protocol adapted for RADOS,
the distributed object storage system that powers Ceph.

More information:

* System Design: http://noahdesu.github.io/2014/10/26/corfu-on-ceph.html
* Asynchronous API Design: http://noahdesu.github.io/2015/09/04/zlog-async-api.html
* Key-Value Store: http://noahdesu.github.io/2016/08/02/zlog-kvstore-intro.html

## Getting Started

* [Building from source](http://noahdesu.github.io/zlog/#building-from-source)
* [Basic operations and documentation are on the wiki](http://noahdesu.github.io/zlog/api/)

## Language Bindings

The base zlog project provides C, C++, and Java bindings.

* C/C++: see `src/include/zlog/`
* Java: see `src/java`
* Go: https://github.com/noahdesu/go-zlog

## Getting Involved

We welcome and encourage people to learn and contribute to the zlog project. If you are looking for ways to get started, we use the [E-easy](https://github.com/noahdesu/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy) and [E-intermediate](https://github.com/noahdesu/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-intermediate) labels to tag issues that are good candidates for new contributors.
