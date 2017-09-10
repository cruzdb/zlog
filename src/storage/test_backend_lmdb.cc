#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"

void BackendTest::SetUp() {
  // create storage backend instance
  // assigned instance to `be`
}

void BackendTest::TearDown() {
  // free backend instance in `be`
}

void LibZLogTest::SetUp() {
  BackendTest::SetUp();
  // create log with backend in `be`
  // assigned log instance to `log`
}

void LibZLogTest::TearDown() {
  // free log instance in `log`
  BackendTest::TearDown();
}
