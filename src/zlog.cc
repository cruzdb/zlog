#include <iostream>
#include <memory>
#include <string>
#include <boost/program_options.hpp>
#include "zlog/backend.h"
#include "zlog/options.h"
#include "libzlog/striper.h"
#include "proto/zlog.pb.h"

namespace po = boost::program_options;

int main(int argc, char **argv)
{
  std::vector<std::string> command;
  std::string log_name;
  std::string backend_name;
  std::string pool;
  std::string db_path;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help", "show help message")
    ("name", po::value<std::string>(&log_name)->default_value("bench"), "log name")
    ("backend", po::value<std::string>(&backend_name)->required(), "backend")
    ("pool", po::value<std::string>(&pool)->default_value("zlog"), "pool (ceph)")
    ("db-path", po::value<std::string>(&db_path)->default_value("/tmp/zlog.bench.db"), "db path (lmdb)")
    ("command", po::value<std::vector<std::string>>(&command), "command")
  ;

  po::positional_options_description popts;
  popts.add("command", -1);

  po::variables_map vm;
  try {
    po::store(po::command_line_parser(argc, argv).options(opts).positional(popts).run(), vm);
    po::notify(vm);
  } catch (const boost::program_options::error &exception) {
    std::cerr << exception.what() << std::endl;
    return 1;
  }

  if (vm.count("help")) {
    std::cout << opts << std::endl;
    return 1;
  }

  zlog::Options options;
  options.backend_name = backend_name;

  if (backend_name == "ceph") {
    options.backend_options["pool"] = pool;
    // zero-length string here causes default path search
    options.backend_options["conf_file"] = "";
  } else if (backend_name == "lmdb") {
    options.backend_options["path"] = db_path;
  }

  std::shared_ptr<zlog::Backend> backend;
  int ret = zlog::Backend::Load(options.backend_name,
      options.backend_options, backend);
  if (ret) {
    std::cerr << "backend::load " << ret << std::endl;
    return ret;
  }

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(log_name, &hoid, &prefix);
  if (ret) {
    std::cerr << "backend::openlog " << ret << std::endl;
    return ret;
  }

  uint64_t epoch = 1;
  while (true) {
    std::map<uint64_t, std::string> views;
    ret = backend->ReadViews(hoid, epoch, 1, &views);
    if (ret) {
      std::cerr << "read views error " << ret << std::endl;
      return ret;
    }

    if (views.empty()) {
      break;
    }

    assert(views.size() == 1u);
    auto it = views.find(epoch);
    assert(it != views.end());

    zlog_proto::View view_src;
    if (!view_src.ParseFromString(it->second)) {
      assert(0);
      exit(1);
    }

    auto view = std::make_shared<zlog::View>(prefix, it->first, view_src);

    std::cout << "view@" << view->epoch() << std::endl;
    for (auto it : view->object_map.stripes()) {
      std::cout << "   stripe@" << it.second.id() << " [" << it.first
        << ", " << it.second.max_position() << "]" << std::endl;
    }

    epoch++;
  }

  return 0;
}
