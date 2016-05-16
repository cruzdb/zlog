#include <iostream>
#include <rados/librados.hpp>
#include "libzlog/log_impl.h" //not sure it is required
#include <map>

class ZlogKV {
  private:
    std::map<std::string, uint64_t> key_to_position_;

    //create zlog object
    zlog::Log *log_;

  public:
    ZlogKV(zlog::Log *log);

    ~ZlogKV();

    void insert(std::string& key, ceph::bufferlist& data);

    void read(std::string key);
};    

