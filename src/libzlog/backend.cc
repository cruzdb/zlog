#include <dlfcn.h>
#include <cerrno>
#include <iostream>
#include <stdlib.h>
#include <limits.h>
#include "include/zlog/backend.h"
#define BE_PREFIX CMAKE_SHARED_LIBRARY_PREFIX "zlog_backend_"
#define BE_SUFFIX CMAKE_SHARED_LIBRARY_SUFFIX

#define BE_ALLOCATE "__backend_allocate"
#define BE_RELEASE "__backend_release"

namespace zlog {

typedef Backend *(*backend_allocate_t)(void);
typedef void (*backend_release_t)(Backend*);

int Backend::Load(const std::string& scheme,
    const std::map<std::string, std::string>& opts,
    std::shared_ptr<Backend>& out_back)
{
  char path[PATH_MAX];
  int ret = snprintf(path, sizeof(path), "%s/" BE_PREFIX "%s" BE_SUFFIX,
      ZLOG_LIBDIR, scheme.c_str());
  if (ret >= (int)sizeof(path))
    return -ENAMETOOLONG;

  auto handle = dlopen(path, RTLD_NOW);
  if (handle == nullptr) {
    const char *libdir = getenv("ZLOG_BE_LIBDIR");
    if (libdir == nullptr)
      libdir = "lib";

    ret = snprintf(path, sizeof(path), "%s/" BE_PREFIX "%s" BE_SUFFIX,
        libdir, scheme.c_str());
    if (ret >= (int)sizeof(path))
      return -ENAMETOOLONG;

    handle = dlopen(path, RTLD_NOW);
    if (handle == nullptr) {
      std::cerr << "could not load backend " << dlerror() << std::endl;
      return -EINVAL;
    }
  }

  auto allocate = (backend_allocate_t)dlsym(handle, BE_ALLOCATE);
  if (allocate == nullptr) {
    dlclose(handle);
    std::cerr << "could not find symbol " << dlerror() << std::endl;
    return -EINVAL;
  }

  auto release = (backend_release_t)dlsym(handle, BE_RELEASE);
  if (release == nullptr) {
    dlclose(handle);
    std::cerr << "could not find symbol " << dlerror() << std::endl;
    return -EINVAL;
  }

  auto backend = allocate();
  if (backend == nullptr)
    return -ENOMEM;

  ret = backend->Initialize(opts);
  if (ret) {
    release(backend);
    dlclose(handle);
    return ret;
  }

  out_back = std::shared_ptr<Backend>(backend, [release, handle](Backend *p) {
    release(p);
    dlclose(handle);
  });

  return 0;
}

}
