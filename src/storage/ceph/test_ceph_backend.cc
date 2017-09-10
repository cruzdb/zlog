#include "storage/test_backend.h"
#include <iostream>

void BackendTest::SetUp() {
  std::cout << "ceph" << std::endl;
}

void BackendTest::TearDown() {
  std::cout << "ceph" << std::endl;
}
