#include "storage/test_backend.h"
#include <iostream>

void BackendTest::SetUp() {
  std::cout << "lmdb" << std::endl;
}

void BackendTest::TearDown() {
  std::cout << "lmdb" << std::endl;
}
