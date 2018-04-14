#pragma once

namespace zlog {

struct Options {
  // Number of objects to stripe the log across. This value is used to configure
  // a new log, and can be adjusted for a log after it has been created.
  // TODO: create an intelligent default
  // TODO: add reference to width adjustment api/tools
  int width = 10;
};

}
