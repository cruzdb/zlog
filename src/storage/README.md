# Create test runner

See `CMakeLists.txt` for linking requirements.

```c++
#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"

void BackendTest::SetUp() {
  // create storage backend instance
  // assigned instance to `backend`
}

void BackendTest::TearDown() {
  // free backend instance in `backend`
}

void LibZLogTest::SetUp() {
  ASSERT_NO_FATAL_FAILURE(BackendTest::SetUp());
  // create log with backend in `backend`
  // assigned log instance to `log`
}

void LibZLogTest::TearDown() {
  // free log instance in `log`
  BackendTest::TearDown();
}
```
