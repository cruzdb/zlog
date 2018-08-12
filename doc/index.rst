===============
Welcome to ZLog
===============

ZLog is a strong consistent shared-log designed to run at high-performance over
distributed storage systems. It is an implementation of the CORFU protocol, and
currently operates on top of the Ceph software-defined storage system (with a
pluggable storage backend).  There are language bindings for C/C++, Java, and
Go.

.. _community:

#########
Community
#########

* Mailing list: https://groups.google.com/group/cruzdb/
* Tracker: https://github.com/cruzdb/zlog/issues

We welcome and encourage people to learn and contribute to the ZLog project.
If you are looking for ways to get started, we use the
`E-easy <https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-easy>`_
and
`E-intermediate <https://github.com/cruzdb/zlog/issues?q=is%3Aissue+is%3Aopen+label%3AE-intermediate>`_
labels to tag issues that are good candidates for new contributors.

####################
Building from source
####################

Clone a copy of the source tree which can be found at
https://github.com/cruzdb/zlog.
When cloning the source repository be sure to use ``--recursive`` to also fetch
the sub-modules. If you forget to use ``--recursive`` then you can fetch them
later using ``git submodule update --init --recursive``.

.. code-block:: bash

    git clone --recursive https://github.com/cruzdb/zlog.git

The base set of dependencies required to build ZLog can be installed by
running the script ``install-dep.sh`` found in the root of the source tree.


.. note::

    The ``install-deps.sh`` has been tested on Fedora, RHEL/CentOS, Ubuntu,
    Debian, and MacOS (using homebrew). Please contact us (see :ref:`community`)
    if you have any issues getting started.

.. code-block:: bash

    cd zlog
    ./install-deps.sh

Once the dependencies have been installed the tree can be built using
``cmake``. By default only the LMDB storage backend will be built. This
is suitable for development and testing, but in order to run ZLog in
production a distributed storage engine such as Ceph should be used.

.. code-block:: bash

    cmake .
    make
    make install

Run a basic set of unit tests using the development backend.  For information on
testing a specific storage engine refer to the documentation on a given
storage engine.

.. code-block:: bash

    ./src/test/zlog_test_backend_lmdb

Next read about the storage engines that ZLog can use to provide
high-performance reliable storage for your log.

##################
More Documentation
##################

.. toctree::
   :maxdepth: 2

   api/index
   storage/index
   options/index
