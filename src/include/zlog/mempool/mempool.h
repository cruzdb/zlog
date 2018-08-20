// -*- mode:C++; tab-width:8; c-basic-offset:2; indent-tabs-mode:t -*-
// vim: ts=8 sw=2 smarttab
/*
 * Ceph - scalable distributed file system
 *
 * Copyright (C) 2016 Allen Samuels <allen.samuels@sandisk.com>
 *
 * This is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License version 2.1, as published by the Free Software
 * Foundation.  See file COPYING.
 *
 */

#ifndef _CEPH_INCLUDE_ZLOG_MEMPOOL_H
#define _CEPH_INCLUDE_ZLOG_MEMPOOL_H

#include <cstddef>
#include <map>
#include <unordered_map>
#include <set>
#include <vector>
#include <list>
#include <mutex>
#include <atomic>
#include <typeinfo>
#include <boost/container/flat_set.hpp>
#include <boost/container/flat_map.hpp>

//#include <zlog/zlog_mempool/Formatter.h>
//#include "include/assert.h"
//#include "include/compact_map.h"
//#include "include/compact_set.h"


/*

Memory Pools
============

A memory pool is a method for accounting the consumption of memory of
a set of containers.

Memory pools are statically declared (see pool_index_t).

Each memory pool tracks the number of bytes and items it contains.

Allocators can be declared and associated with a type so that they are
tracked independently of the pool total.  This additional accounting
is optional and only incurs an overhead if the debugging is enabled at
runtime.  This allows developers to see what types are consuming the
pool resources.


Declaring
---------

Using memory pools is very easy.

To create a new memory pool, simply add a new name into the list of
memory pools that's defined in "DEFINE_MEMORY_POOLS_HELPER".  That's
it.  :)

For each memory pool that's created a C++ namespace is also
automatically created (name is same as in DEFINE_MEMORY_POOLS_HELPER).
That namespace contains a set of common STL containers that are predefined
with the appropriate allocators.

Thus for zlog_mempool "osd" we have automatically available to us:

   zlog_mempool::osd::map
   zlog_mempool::osd::multimap
   zlog_mempool::osd::set
   zlog_mempool::osd::multiset
   zlog_mempool::osd::list
   zlog_mempool::osd::vector
   zlog_mempool::osd::unordered_map


Putting objects in a zlog_mempool
----------------------------

In order to use a memory pool with a particular type, a few additional
declarations are needed.

For a class:

  struct Foo {
    ZLOG_MEMPOOL_CLASS_HELPERS();
    ...
  };

Then, in an appropriate .cc file,

  ZLOG_MEMPOOL_DEFINE_OBJECT_FACTORY(Foo, foo, osd);

The second argument can generally be identical to the first, except
when the type contains a nested scope.  For example, for
BlueStore::Onode, we need to do

  ZLOG_MEMPOOL_DEFINE_OBJECT_FACTORY(BlueStore::Onode, bluestore_onode,
                                bluestore_meta);

(This is just because we need to name some static variables and we
can't use :: in a variable name.)

XXX Note: the new operator hard-codes the allocation size to the size of the
object given in ZLOG_MEMPOOL_DEFINE_OBJECT_FACTORY. For this reason, you cannot
incorporate zlog_mempools into a base class without also defining a helper/factory
for the child class as well (as the base class is usually smaller than the
child class).

In order to use the STL containers, simply use the namespaced variant
of the container type.  For example,

  zlog_mempool::osd::map<int> myvec;

Introspection
-------------

The simplest way to interrogate the process is with

  Formater *f = ...
  zlog_mempool::dump(f);

This will dump information about *all* memory pools.  When debug mode
is enabled, the runtime complexity of dump is O(num_shards *
num_types).  When debug name is disabled it is O(num_shards).

You can also interrogate a specific pool programmatically with

  size_t bytes = zlog_mempool::unittest_2::allocated_bytes();
  size_t items = zlog_mempool::unittest_2::allocated_items();

The runtime complexity is O(num_shards).

Note that you cannot easily query per-type, primarily because debug
mode is optional and you should not rely on that information being
available.

*/

namespace zlog_mempool {

// --------------------------------------------------------------
// define memory pools

#define DEFINE_MEMORY_POOLS_HELPER(f) \
  f(cache)


// give them integer ids
#define P(x) zlog_mempool_##x,
enum pool_index_t {
  DEFINE_MEMORY_POOLS_HELPER(P)
  num_pools        // Must be last.
};
#undef P

extern bool debug_mode;
extern void set_debug_mode(bool d);

// --------------------------------------------------------------
class pool_t;

// we shard pool stats across many shard_t's to reduce the amount
// of cacheline ping pong.
enum {
  num_shard_bits = 5
};
enum {
  num_shards = 1 << num_shard_bits
};

// align shard to a cacheline
struct shard_t {
  std::atomic<size_t> bytes = {0};
  std::atomic<size_t> items = {0};
  char __padding[128 - sizeof(std::atomic<size_t>)*2];
} __attribute__ ((aligned (128)));

static_assert(sizeof(shard_t) == 128, "shard_t should be cacheline-sized");

struct stats_t {
  ssize_t items = 0;
  ssize_t bytes = 0;
  // void dump(ceph::Formatter *f) const {
  //   f->dump_int("items", items);
  //   f->dump_int("bytes", bytes);
  // }

  stats_t& operator+=(const stats_t& o) {
    items += o.items;
    bytes += o.bytes;
    return *this;
  }
};

pool_t& get_pool(pool_index_t ix);
const char *get_pool_name(pool_index_t ix);

struct type_t {
  const char *type_name;
  size_t item_size;
  std::atomic<ssize_t> items = {0};  // signed
};

struct type_info_hash {
  std::size_t operator()(const std::type_info& k) const {
    return k.hash_code();
  }
};

class pool_t {
  shard_t shard[num_shards];

  mutable std::mutex lock;  // only used for types list
  std::unordered_map<const char *, type_t> type_map;

public:
  //
  // How much this pool consumes. O(<num_shards>)
  //
  size_t allocated_bytes() const;
  size_t allocated_items() const;

  void adjust_count(ssize_t items, ssize_t bytes);

  shard_t* pick_a_shard() {
    // Dirt cheap, see:
    //   http://fossies.org/dox/glibc-2.24/pthread__self_8c_source.html
    size_t me = (size_t)pthread_self();
    size_t i = (me >> 3) & ((1 << num_shard_bits) - 1);
    return &shard[i];
  }

  type_t *get_type(const std::type_info& ti, size_t size) {
    std::lock_guard<std::mutex> l(lock);
    auto p = type_map.find(ti.name());
    if (p != type_map.end()) {
      return &p->second;
    }
    type_t &t = type_map[ti.name()];
    t.type_name = ti.name();
    t.item_size = size;
    return &t;
  }

  // get pool stats.  by_type is not populated if !debug
  void get_stats(stats_t *total,
		 std::map<std::string, stats_t> *by_type) const;

  //void dump(ceph::Formatter *f, stats_t *ptotal=0) const;
};

//void dump(ceph::Formatter *f);


// STL allocator for use with containers.  All actual state
// is stored in the static pool_allocator_base_t, which saves us from
// passing the allocator to container constructors.

template<pool_index_t pool_ix, typename T>
class pool_allocator {
  pool_t *pool;
  type_t *type = nullptr;

public:
  typedef pool_allocator<pool_ix, T> allocator_type;
  typedef T value_type;
  typedef value_type *pointer;
  typedef const value_type * const_pointer;
  typedef value_type& reference;
  typedef const value_type& const_reference;
  typedef std::size_t size_type;
  typedef std::ptrdiff_t difference_type;

  template<typename U> struct rebind {
    typedef pool_allocator<pool_ix,U> other;
  };

  void init(bool force_register) {
    pool = &get_pool(pool_ix);
    if (debug_mode || force_register) {
      type = pool->get_type(typeid(T), sizeof(T));
    }
  }

  pool_allocator(bool force_register=false) {
    init(force_register);
  }
  template<typename U>
  pool_allocator(const pool_allocator<pool_ix,U>&) {
    init(false);
  }

  T* allocate(size_t n, void *p = nullptr) {
    size_t total = sizeof(T) * n;
    shard_t *shard = pool->pick_a_shard();
    shard->bytes += total;
    shard->items += n;
    if (type) {
      type->items += n;
    }
    T* r = reinterpret_cast<T*>(new char[total]);
    return r;
  }

  void deallocate(T* p, size_t n) {
    size_t total = sizeof(T) * n;
    shard_t *shard = pool->pick_a_shard();
    shard->bytes -= total;
    shard->items -= n;
    if (type) {
      type->items -= n;
    }
    delete[] reinterpret_cast<char*>(p);
  }

  T* allocate_aligned(size_t n, size_t align, void *p = nullptr) {
    size_t total = sizeof(T) * n;
    shard_t *shard = pool->pick_a_shard();
    shard->bytes += total;
    shard->items += n;
    if (type) {
      type->items += n;
    }
    char *ptr;
    int rc = ::posix_memalign((void**)(void*)&ptr, align, total);
    if (rc)
      throw std::bad_alloc();
    T* r = reinterpret_cast<T*>(ptr);
    return r;
  }

  void deallocate_aligned(T* p, size_t n) {
    size_t total = sizeof(T) * n;
    shard_t *shard = pool->pick_a_shard();
    shard->bytes -= total;
    shard->items -= n;
    if (type) {
      type->items -= n;
    }
    ::free(p);
  }

  void destroy(T* p) {
    p->~T();
  }

  template<class U>
  void destroy(U *p) {
    p->~U();
  }

  void construct(T* p, const T& val) {
    ::new ((void *)p) T(val);
  }

  template<class U, class... Args> void construct(U* p,Args&&... args) {
    ::new((void *)p) U(std::forward<Args>(args)...);
  }

  bool operator==(const pool_allocator&) const { return true; }
  bool operator!=(const pool_allocator&) const { return false; }
};


// Namespace zlog_mempool

#define P(x)								\
  namespace x {								\
    static const zlog_mempool::pool_index_t id = zlog_mempool::zlog_mempool_##x;	\
    template<typename v>						\
    using pool_allocator = zlog_mempool::pool_allocator<id,v>;		\
                                                                        \
    using string = std::basic_string<char,std::char_traits<char>,       \
                                     pool_allocator<char>>;             \
                                                                        \
    template<typename k,typename v, typename cmp = std::less<k> >	\
    using map = std::map<k, v, cmp,					\
			 pool_allocator<std::pair<const k,v>>>;		\
                                                    \
    template<typename k,typename v, typename cmp = std::less<k> >	\
    using multimap = std::multimap<k,v,cmp,				\
				   pool_allocator<std::pair<const k,	\
							    v>>>;	\
                                                                        \
    template<typename k, typename cmp = std::less<k> >			\
    using set = std::set<k,cmp,pool_allocator<k>>;			\
                                                                        \
    template<typename k, typename cmp = std::less<k> >			\
    using flat_set = boost::container::flat_set<k,cmp,pool_allocator<k>>; \
									\
    template<typename k, typename v, typename cmp = std::less<k> >	\
    using flat_map = boost::container::flat_map<k,v,cmp,		\
						pool_allocator<std::pair<k,v>>>; \
                                                                        \
    template<typename v>						\
    using list = std::list<v,pool_allocator<v>>;			\
                                                                        \
    template<typename v>						\
    using vector = std::vector<v,pool_allocator<v>>;			\
                                                                        \
    template<typename k, typename v,					\
	     typename h=std::hash<k>,					\
	     typename eq = std::equal_to<k>>				\
    using unordered_map =						\
      std::unordered_map<k,v,h,eq,pool_allocator<std::pair<const k,v>>>;\
                                                                        \
    inline size_t allocated_bytes() {					\
      return zlog_mempool::get_pool(id).allocated_bytes();			\
    }									\
    inline size_t allocated_items() {					\
      return zlog_mempool::get_pool(id).allocated_items();			\
    }									\
  };

DEFINE_MEMORY_POOLS_HELPER(P)

#undef P

};

// the elements allocated by zlog_mempool is in the same memory space as the ones
// allocated by the default allocator. so compare them in an efficient way:
// libstdc++'s std::equal is specialized to use memcmp if T is integer or
// pointer. this is good enough for our usecase. use
// std::is_trivially_copyable<T> to expand the support to more types if
// nececssary.
template<typename T, zlog_mempool::pool_index_t pool_index>
bool operator==(const std::vector<T, std::allocator<T>>& lhs,
		const std::vector<T, zlog_mempool::pool_allocator<pool_index, T>>& rhs)
{
  return (lhs.size() == rhs.size() &&
	  std::equal(lhs.begin(), lhs.end(), rhs.begin()));
}

template<typename T, zlog_mempool::pool_index_t pool_index>
bool operator!=(const std::vector<T, std::allocator<T>>& lhs,
		const std::vector<T, zlog_mempool::pool_allocator<pool_index, T>>& rhs)
{
  return !(lhs == rhs);
}

template<typename T, zlog_mempool::pool_index_t pool_index>
bool operator==(const std::vector<T, zlog_mempool::pool_allocator<pool_index, T>>& lhs,
		const std::vector<T, std::allocator<T>>& rhs)
{
  return rhs == lhs;
}

template<typename T, zlog_mempool::pool_index_t pool_index>
bool operator!=(const std::vector<T, zlog_mempool::pool_allocator<pool_index, T>>& lhs,
		const std::vector<T, std::allocator<T>>& rhs)
{
  return !(lhs == rhs);
}

// Use this for any type that is contained by a container (unless it
// is a class you defined; see below).
#define ZLOG_MEMPOOL_DECLARE_FACTORY(obj, factoryname, pool)			\
  namespace zlog_mempool {							\
    namespace pool {							\
      extern pool_allocator<obj> alloc_##factoryname;			\
    }									\
  }

#define ZLOG_MEMPOOL_DEFINE_FACTORY(obj, factoryname, pool)			\
  namespace zlog_mempool {							\
    namespace pool {							\
      pool_allocator<obj> alloc_##factoryname = {true};			\
    }									\
  }

// Use this for each class that belongs to a zlog_mempool.  For example,
//
//   class T {
//     ZLOG_MEMPOOL_CLASS_HELPERS();
//     ...
//   };
//
#define ZLOG_MEMPOOL_CLASS_HELPERS()						\
  void *operator new(size_t size);					\
  void *operator new[](size_t size) noexcept {				\
    assert(0 == "no array new");					\
    return nullptr; }							\
  void  operator delete(void *);					\
  void  operator delete[](void *) { assert(0 == "no array delete"); }


// Use this in some particular .cc file to match each class with a
// ZLOG_MEMPOOL_CLASS_HELPERS().
#define ZLOG_MEMPOOL_DEFINE_OBJECT_FACTORY(obj,factoryname,pool)		\
  ZLOG_MEMPOOL_DEFINE_FACTORY(obj, factoryname, pool)			\
  void *obj::operator new(size_t size) {				\
    return zlog_mempool::pool::alloc_##factoryname.allocate(1); \
  }									\
  void obj::operator delete(void *p)  {					\
    return zlog_mempool::pool::alloc_##factoryname.deallocate((obj*)p, 1);	\
  }

#endif
