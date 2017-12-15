# ZLog - a fast distributed shared log

[![Build Status](https://travis-ci.org/cruzdb/zlog.svg?branch=master)](https://travis-ci.org/cruzdb/zlog)
[![Coverity Scan Build Status](https://scan.coverity.com/projects/9894/badge.svg)](https://scan.coverity.com/projects/cruzdb-zlog)
[![codecov](https://codecov.io/gh/cruzdb/zlog/branch/master/graph/badge.svg)](https://codecov.io/gh/cruzdb/zlog)
[![docs](https://img.shields.io/badge/docs-latest-brightgreen.svg?style=flat)](https://cruzdb.github.io/zlog)

ZLog is a high-performance, strongly consistent shared-log. Currently ZLog runs
on top of the Ceph and RADOS distributed storage system, but supports plugging
in additional storage targets. Its goal is to replicate the CORFU protocol
adapted for software-defined storage.

More information:

* System Design: https://nwat.io/blog/2014/10/26/zlog-a-distributed-shared-log-on-ceph/
* Asynchronous API Design: https://nwat.io/blog/2015/09/04/zlog-asynchronous-i/o-support/
* Key-Value Store: https://nwat.io/blog/2016/08/02/introduction-to-the-zlog-transaction-key-value-store/

**The project is undergoing a transition to https://github.com/cruzdb
organization. Please let us know if we notice any broken links!**

## Getting Started

* [Building from source](http://cruzdb.github.io/zlog/#building-from-source)
* [Basic operations and documentation are on the wiki](http://cruzdb.github.io/zlog/api/)
* Mailing list: https://groups.google.com/group/cruzdb/

## Language Bindings

The base ZLog project provides C, C++, and Java bindings.

* C/C++: see `src/include/zlog/`
* Java: see `src/java`
* Go: https://github.com/cruzdb/go-zlog

## Getting Involved

We welcome and encourage people to learn and contribute to the ZLog project. If you are looking for ways to get started, we use the [E-easy](https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy) and [E-intermediate](https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-intermediate) labels to tag issues that are good candidates for new contributors.

## Build Status

| Distribution     | Status |
| ------------     | ------ |
| CentOS 7         | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=centos:7&label=centos:7)](https://travis-ci.org/cruzdb/zlog) |
| Debian Jessie    | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=debian:jessie&label=debian:jessie)](https://travis-ci.org/cruzdb/zlog) |
| Ubuntu 14.04 LTS | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=ubuntu:trusty&label=ubuntu:trusty)](https://travis-ci.org/cruzdb/zlog) |
| Ubuntu 16.04 LTS | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=ubuntu:xenial&label=ubuntu:xenial)](https://travis-ci.org/cruzdb/zlog) |
| Ubuntu 16.10     | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=ubuntu:yakkety&label=ubuntu:yakkety)](https://travis-ci.org/cruzdb/zlog) |
| Ubuntu 17.04     | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=ubuntu:zesty+RUN_COVERAGE=0&label=ubuntu:zesty)](https://travis-ci.org/cruzdb/zlog) |
| Fedora 24        | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=fedora:24&label=fedora:24)](https://travis-ci.org/cruzdb/zlog) |
| Fedora 25        | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=fedora:25&label=fedora:25)](https://travis-ci.org/cruzdb/zlog) |
| Fedora 26        | [![status](https://badges.herokuapp.com/travis/cruzdb/zlog?env=DOCKER_IMAGE=fedora:26&label=fedora:26)](https://travis-ci.org/cruzdb/zlog) |
