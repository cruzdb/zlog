================
Storage Backends
================

The development backend is meant for testing and development, and the Ceph
backend is designed to provide high-performance and reliability.

###################
Development Backend
###################

The development backend is built-in, so there are no special build
instructions. It is currently limited to single-process test cases. There is
an open ticket for using LMDB to provide a development backend that will
support multi-process and sequencer testing (see
https://github.com/noahdesu/zlog/issues/108).

##############
Ceph and RADOS
##############

Running ZLog on Ceph provides high-performance, durability, and scalability.
In order to use Ceph the ZLog library must be built with Ceph support, and a
special ZLog plugin loaded into your Ceph cluster.

The ZLog tree will build with Ceph support automatically if the RADOS
development packages are installed. Typically this can be accomplished using
your package manager of choice.

.. code-block:: bash

    apt-get install librados-dev

    # or on fedora/rhel/centos:
    yum install -y librados-devel

.. note::

    Please refer to the `Ceph documentation <https://ceph.com/docs>`_ for
    complete instructions on installing Ceph on your platform.

Once the RADOS development package is installed run (or re-run) CMake and
build. The build system should report that RADOS was found and that the Ceph
backend will be built.

.. code-block:: bash

    cmake .
    # -- Found LIBRADOS: /usr/lib/librados.so  
    # -- Building Ceph backend /usr/lib/librados.so
    make

That's it. Now ZLog can communicate with Ceph, but the Ceph plugin still needs
to be built and installed.

.. note::

    As of February 2017 work has begun on a Ceph plugin framework that will
    significantly simplify the process of building and installing a Ceph
    plugin. Please get in touch with us if you have any issues with the
    current instructions. Thanks!

********************
Docker image builder
********************

Our continuous integration suite always builds the Ceph plugin from scratch
using a Docker container. This has the added benefit of completely
documenting the process of how to build the plugin. We recommend first using
this container to build the plugin. It is currently configured to build with
Ubuntu, but we can provide additional images on demand (see :ref:`community`
to get in touch with us).

This is an example of how the plugin can be built with the Docker image
located https://github.com/noahdesu/zlog/tree/master/docker/ceph-plugin.

.. code-block:: bash

    mkdir ~/ceph-plugin/
    docker run -v ~/ceph-plugin:/ceph_zlog_plugin zlog/ceph-plugin:latest

After running the Docker image a set of ``libcls_zlog.so*`` object files
should be present in the ``~/ceph-plugin/`` directory.

********************
Building from source
********************

We would like to avoid duplicating the instructions for building the plugin.
If you find that the Docker image instructions above do not meet your needs
please let us know and we can update them or provide instructions to meet your
specific needs.

**************************
Installing the Ceph plugin
**************************

The Ceph plugin library needs to be copied onto each OSD in your cluster.

.. code-block:: bash

    sudo cp -a ~/ceph-plugin/libcls_zlog.so* /usr/lib/rados-classes

    # or on fedora/rhel/centos
    sudo cp -a ~/ceph-plugin/libcls_zlog.so* /usr/lib64/rados-classes

.. note::

    If the ZLog plugin is being updated then each OSD needs to be restarted to
    pick-up the new plugin version. Don't forget to update 'osd class load
    list' and 'osd class default list' in your ceph.conf to allow the ZLog
    plugin to be loaded.

*********************
Run Ceph-backed tests
*********************

Once everything is setup test out the Ceph backend by running the unit tests.
You'll need to start the ZLog sequencer for these tests.

.. code-block:: bash

  zlog-seqr --port 5678 --streams --daemon
  zlog-test-cls-zlog
  zlog-test-ceph
