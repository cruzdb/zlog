================
Storage Backends
================

The development backend is meant for testing and development, and the Ceph
backend is designed to provide high-performance and reliability.

###################
Development Backend
###################

There are two development backends available, one that stores the entire log
in RAM, and one that stores the log in an LMDB database. Both are are built-in
automatically so there are no additional steps required to make these backends
available.

############
Ceph Backend
############

Running ZLog on Ceph provides high-performance, durability, and scalability.
In order to use Ceph the ZLog library must be built with Ceph support, and a
special ZLog plugin loaded into your Ceph cluster.

Building ZLog With Ceph Support
-------------------------------

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

Building the Ceph Plugin
------------------------

The easiest way to build the Ceph plugin is to use the `build-ceph-plugin.sh`
script found in the ZLog source tree. This script builds the plugin for a
variety of OS distributions and Ceph versions.

The following example shows how to use the script to build the plugin for
the Ceph `luminous` release targetting an OSD running `ubuntu:xenial`. After
the build completes the plugin can be found in a local directory named
`libcls_zlog_ubuntu<identifier>`:

.. code-block:: bash

    $> docker/build-ceph-plugin.sh -i ubuntu:xenial -c luminous

    [nwatkins@martini zlog]$ ls -l libcls_zlog_ubuntu\:xenial.luminous/
    total 740
    lrwxrwxrwx. 1 nwatkins nwatkins     16 Jun  5 22:37 libcls_zlog.so -> libcls_zlog.so.1
    lrwxrwxrwx. 1 nwatkins nwatkins     20 Jun  5 22:37 libcls_zlog.so.1 -> libcls_zlog.so.1.0.0
    -rwxr-xr-x. 1 nwatkins nwatkins 754704 Jun  5 22:37 libcls_zlog.so.1.0.0

The `build-ceph-plugin.sh` script has been tested with the following
configurations. Please contact us if you need a different configuration, such
as support for an older version of Ceph (see :ref:`community` to get in touch
with us).

* Luminous v12.0.0 (or newer)
    * ubuntu:{trusty,xenial}
    * debian:jessie
    * fedora:{24,25}
    * centos:7

Installation
------------

The Ceph plugin library needs to be copied onto each OSD in your cluster so
that Ceph can find it at runtime.  In the code snippet below the folder
containing the plugin, `libcls_zlog_<identifer>` will be named according to
the configuration it was built with. For example,
`libcls_zlog_ubuntu:xenial_luminous`. Copy the libraries into the
`rados-classes` directory, found at `/usr/lib/rados-classes` and Debian-based
systems, and `/usr/lib64/rados-classes` on Fedora, CentOS, and RHEL.

.. code-block:: bash

    sudo cp -a libcls_zlog_<identifer>/libcls_zlog.so* /usr/lib/rados-classes

    # or on fedora/rhel/centos
    sudo cp -a libcls_zlog_<identifer>/libcls_zlog.so* /usr/lib64/rados-classes

.. important::

    The plugin requires (1) Google Protocol buffers to be installed on the OSDs,
    and (2) Ceph must be configured to support external plugins. See next:

Install Google Protocol Buffers using your system's package manager. This must
be done on each node in the system running an OSD:

.. code-block:: bash

    # Debian-based systems
    apt-get install libprotobuf-dev

    # CentOS, Fedora, RHEL
    yum install protobuf-devel

Configure Ceph to allow external plugins by adding the following to
`ceph.conf`, either system wide or locally on each OSD ndoe.

.. code-block:: bash

    osd class load list = *
    osd class default list = *

.. note::

    Each OSD needs to be restarted after editing the `ceph.conf`
    configuration. After installing the plugin, each OSD needs to be restarted
    only if the installation is an upgrade of the plugin.

*********************
Run Ceph-backed tests
*********************

Once everything is setup test out the Ceph backend by running the unit tests.
You'll need to start the ZLog sequencer for these tests.

.. code-block:: bash

  zlog-seqr --port 5678 --streams --daemon
  zlog-test-cls-zlog
  zlog-test-ceph
