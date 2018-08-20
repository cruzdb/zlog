=======
Options
=======
The options structure, defined in options.h allows you to configure the following:

Options:

Width
	The number of objects per stripe.
Entries per object
	The number of entries stores in each object
Max entry size
	The maximum size allowed for an individual entry
Statistics
	A pointer to a cache statistics object, created with ``zlog::CreateCacheStatistics()``
Http
	A vector of strings that contains the configuration to expose the cache statistics through an embedded http server
Eviction
	Enumerate that describes the eviction policy to be used by the cache
Cache size
	The maximum number of entries that the cache will hold. 


Types and deaults:

.. code-block:: c++

    int width = 10;
    int entries_per_object = 200;
    int max_entry_size = 1024;
    std::shared_ptr<Statistics> statistics = nullptr;
    std::vector<std::string> http;
    zlog::Eviction::Eviction_Policy eviction = zlog::Eviction::Eviction_Policy::LRU;
    size_t cache_size = 1024 * 1024 * 1;
	

#############
Cache options
#############

Eviction policies
-----------------
The cahce implements currently 2 eviction policies 

- LRU (Least Recently Used)

.. code-block:: c++

    options.eviction = zlog::Eviction::Eviction_Policy::LRU;

- ARC (Adaptive Replacement Cache(don't tell IBM))

.. code-block:: c++

    options.eviction = zlog::Eviction::Eviction_Policy::ARC;

The eviction policies are built on top of an abstract layer, so that building your own eviction policies is really simple as long as you implement the abstract interface.

.. code-block:: c++

    virtual int cache_get_hit(uint64_t* pos) = 0;
    virtual int cache_get_miss(uint64_t pos) = 0;
    virtual int cache_put_miss(uint64_t pos) = 0;
    virtual uint64_t get_evicted() = 0;

Cache size
----------
The size of the cache can be configured by modifing the ``cache_size`` field:

.. code-block:: c++

    options.cache_size = 1024;
    
Note that this is not the size in bytes of the cache, but the maximum number of entries that will be stored at any given time on the cache.

.. note::

	The cache will only be available if zlog is built with the WITH_CACHE macro.
	You can define it using the CMake configuration ``add_definitions(-DWITH_CACHE)``

################
Cache statistics
################

Currenlty ZLog provides a way to measure in real time these statistics of the cache:
    
- Number of cache requierments
- Number of cache hits

How to use
----------

Setup options.statistics

.. code-block:: c++

    options.statistics = zlog::CreateCacheStatistics();
    
Setup http options to expose the statistics

.. code-block:: c++

    options.http = std::vector<std::string>({"listening_ports", "0.0.0.0:8080", "num_threads", "1"});
    
Then you will be able to read the current stats by accessing ``localhost:8080`` from a browser.

.. note::

	The cache statistics will only be available if zlog is built with the WITH_STATS macro.
	You can define it using the CMake configuration ``add_definitions(-DWITH_STATS)``
