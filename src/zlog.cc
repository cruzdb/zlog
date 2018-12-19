#include <iostream>
#include <memory>
#include <string>
#include <boost/program_options.hpp>
#include "zlog/backend.h"
#include "zlog/log.h"
#include "zlog/options.h"
#include "libzlog/striper.h"
#include "proto/zlog.pb.h"

namespace po = boost::program_options;

int handle_log(std::vector<std::string>, std::shared_ptr<zlog::Backend>);

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

  // This gives us a vector of the command line arguments with flags removed
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

  if (command.size() > 0) {
    if (command[0] == "log") {
      auto subcommand = std::vector<std::string>(command.begin() + 1, command.end());
      return handle_log(subcommand, backend);
    }
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

/*
 * Handles log commands and returns an exit code. The accepted commands are
 * - create <log name>
 * - append <log name>
 * - dump <log name>
 * - trim <log name>
 * - fill <log name>
 * - rename <log name> <new log name>
 *
 * @param command the command to execute
 * @param backend the backend to use
 *
 * @return exit code
 */
int handle_log(std::vector<std::string> command, std::shared_ptr<zlog::Backend> backend) {
  const static std::map<std::string, std::string> usages = {
          { "create", "zlog log create <log name>" },
          { "append", "zlog log append <log name>" },
          { "dump", "zlog log dump <log name>" },
          { "trim", "zlog log trim <log name> <position>" },
          { "fill", "zlog log fill <log name> <position>" },
          { "rename", "zlog log rename <log name> <new log name>" },
  };

  if (command.size() == 0 || usages.find(command[0]) == usages.end()) {
    std::cerr << "usage:" << std::endl;
    for (const auto &usage : usages) {
      std::cerr << usage.second << std::endl;
    }
    return 1;
  }

  if (command[0] == "create") {
    if (command.size() != 2) { // create <log name>
      std::cerr << usages.at("create") << std::endl;
      return 1;
    }
    std::string hoid, prefix;
    int ret = backend->CreateLog(command[1], "", &hoid, &prefix);
    switch (ret) {
      case 0:
        break;
      case -EEXIST:
        std::cerr << "error: log name already exists" << std::endl;
        return ret;
      case -EINVAL:
        std::cerr << "error: invalid input" << std::endl;
        return ret;
      default:
        std::cerr << "error: unknown error" << std::endl;
        return ret;
    }
    std::cout << hoid << std::endl << prefix << std::endl;
    return 0;
  }

  // The rest of the commands need an opened log
  zlog::Log *plog;
  zlog::Options options;
  options.backend = backend;
  int ret = zlog::Log::Open(options, command[1], &plog);
  switch (ret) {
    case 0:
      break;
    case -ENOENT:
      std::cerr << "error: no log named \"" + command[1] + "\"" << std::endl;
      return ret;
    case -EINVAL:
      std::cerr << "error: invalid input" << std::endl;
    default:
      std::cerr << "error: unknown error " << ret << std::endl;
      return ret;
  }
  std::unique_ptr<zlog::Log> log(plog);

  if (command[0] == "append") {
    if (command.size() != 2) { // append <log name>
      std::cerr << usages.at("append") << std::endl;
      return 1;
    }
    uint64_t tail;
    int ret = log->CheckTail(&tail);
    if (ret != 0) {
      std::cerr << "log::CheckTail " << ret << std::endl;
      return ret;
    }
    std::string data;
    while (std::getline(std::cin, data)) { // Extra lines at end of file possible
      int ret = log->Append(data, &tail);
      if (ret != 0) {
        std::cerr << "log::Append " << ret << std::endl;
        return ret;
      }
    }
    return 0;
  } else if (command[0] == "dump") {
    if (command.size() != 2) { // dump <log name>
      std::cerr << usages.at("dump") << std::endl;
      return 1;
    }
    uint64_t tail;
    int ret = log->CheckTail(&tail);
    if (ret != 0) {
      std::cerr << "log::CheckTail " << ret << std::endl;
      return ret;
    }
    std::string data;
    for (uint64_t i = 0; i < tail; ++i) {
      int ret = log->Read(i, &data);
      if (ret != 0) {
        std::cerr << "log::Read " << ret << std::endl;
        return ret;
      }
      std::cout << data << std::endl;
    }
    return 0;
  } else if (command[0] == "trim") {
    if (command.size() != 3) { // trim <log name> <position>
      std::cerr << usages.at("trim") << std::endl;
      return 1;
    }
    uint64_t pos;
    try {
      pos = std::stoul(command[2]);
    } catch (const std::invalid_argument &e) {
      std::cerr << e.what() << std::endl;
      return 1;
    }
    int ret = log->Trim(pos);
    if (ret != 0) {
      std::cerr << "log::Trim " << ret << std::endl;
    }
    return ret;
  } else if (command[0] == "fill") {
    if (command.size() != 3) { // fill <log name> <position>
      std::cerr << usages.at("fill") << std::endl;
      return 1;
    }
    uint64_t pos;
    try {
      pos = std::stoul(command[2]);
    } catch (const std::invalid_argument &e) {
      std::cerr << e.what() << std::endl;
      return 1;
    }
    int ret = log->Fill(pos);
    if (ret != 0) {
      std::cerr << "log::Fill " << ret << std::endl;
    }
    return ret;
  } else if (command[0] == "rename") {
    if (command.size() != 3) { // rename <old log name> <new log name>
      std::cerr << usages.at("rename") << std::endl;
      return 1;
    }
    std::cerr << "Not implemented" << std::endl;
    return 0;
  }
  // Should never reach here, but just to be safe
  std::cerr << "usage:" << std::endl;
  for (const auto &usage : usages) {
    std::cerr << usage.second << std::endl;
  }
  return 1;
}