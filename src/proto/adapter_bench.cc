#include <algorithm>
#include <iostream>
#include <random>
#include <fstream>
#include <string>
#include <time.h>
#include <rados/buffer.h>
#include "proto/adapter_test.pb.h"
#include "proto/protobuf_bufferlist_adapter.h"

#define MAX_SHIFT 22
#define NUM_RUNS 100

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  int ret = clock_gettime(clock, &ts);
  assert(ret == 0);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getns()
{
  return __getns(CLOCK_MONOTONIC);
}

int main(int argc, char **argv)
{
  // create random data to use for payloads
  size_t rand_buf_size = (size_t)1 << (MAX_SHIFT+2);
  std::string rand_buf;
  rand_buf.reserve(rand_buf_size);
  std::ifstream ifs("/dev/urandom", std::ios::binary | std::ios::in);
  std::copy_n(std::istreambuf_iterator<char>(ifs),
      rand_buf_size, std::back_inserter(rand_buf));
  const char *rand_buf_raw = rand_buf.c_str();

  // grab random slices from the random bytes
  std::default_random_engine generator;
  std::uniform_int_distribution<int> rand_dist;
  rand_dist = std::uniform_int_distribution<int>(0,
      rand_buf_size - ((size_t)1<<MAX_SHIFT) - 1);

  for (int shift = 0; shift <= MAX_SHIFT; shift++) {
    auto startns = getns();
    size_t size = shift ? ((size_t)1 << shift) : 0;
    for (int run = 0; run < NUM_RUNS; run++) {
      size_t buf_offset = rand_dist(generator);

      adapter_test::TestMessage m;
      m.set_num(size);
      if (size) {
        m.set_data(rand_buf_raw + buf_offset, size);
      }

      ceph::bufferlist bl;
      pack_msg<adapter_test::TestMessage>(bl, m);
    }
    auto totalns = getns() - startns;
    auto avgus = totalns / 1000;
    std::cout << size << " " << avgus << std::endl;
  }
}
