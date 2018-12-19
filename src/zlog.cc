#include <iomanip>
#include <iostream>
#include <memory>
#include <fstream>
#include <string>
#include <boost/program_options.hpp>
#include "zlog/backend.h"
#include "zlog/log.h"
#include "zlog/options.h"
#include "libzlog/striper.h"
#include "proto/zlog.pb.h"

namespace po = boost::program_options;

int handle_log(std::vector<std::string>, std::shared_ptr<zlog::Backend>, std::string);

int main(int argc, char **argv)
{
  std::vector<std::string> command;
  std::string log_name;
  std::string backend_name;
  std::string pool;
  std::string db_path;
  std::string input_filename;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help", "show help message")
    ("name", po::value<std::string>(&log_name)->default_value("bench"), "log name")
    ("backend", po::value<std::string>(&backend_name)->required(), "backend")
    ("pool", po::value<std::string>(&pool)->default_value("zlog"), "pool (ceph)")
    ("db-path", po::value<std::string>(&db_path)->default_value("/tmp/zlog.bench.db"), "db path (lmdb)")
    ("command", po::value<std::vector<std::string>>(&command), "command")
    ("input-file,i", po::value<std::string>(&input_filename), "input filename for log append")
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
      return handle_log(subcommand, backend, input_filename);
    }
  }

  if (command == std::vector<std::string>{ "link", "list" }) {
    std::vector<std::string> links;
    int ret = backend->ListLinks(links);
    if (ret != 0) {
      std::cerr << "backend::ListLinks " << ret << std::endl;
      return ret;
    }
    for (const auto &link : links) {
      std::cout << link << std::endl;
    }
    return 0;
  } else if (command == std::vector<std::string>{ "head", "list" }) {
    std::vector<std::string> heads;
    int ret = backend->ListHeads(heads);
    if (ret != 0) {
      std::cerr << "backend::ListHeads " << ret << std::endl;
      return ret;
    }
    for (const auto &head : heads) {
      std::cout << head << std::endl;
    }
    return 0;
  }

  std::cerr << "usage:" << std::endl
            << "zlog log ..." << std::endl
            << "zlog link list" << std::endl
            << "zlog head list" << std::endl;
  return 1;
}

/*
 * Handles log commands and returns an exit code. The accepted commands are
 * - create <log name>
 * - append <log name>
 * - dump <log name>
 * - trim <log name>
 * - fill <log name>
 *
 * @param command  the command to execute
 * @param backend  the backend to use
 * @param filename the input filename for append commands
 *
 * @return exit code
 */
int handle_log(std::vector<std::string> command, std::shared_ptr<zlog::Backend> backend, std::string filename) {
  const static std::map<std::string, std::string> usages = {
          { "create", "zlog log create <log name>" },
          { "append", "zlog log append <log name> <string>\nzlog log append <log name> -i <filename>" },
          { "dump", "zlog log dump <log name>" },
          { "read", "zlog log read <log name> <position>" },
          { "trim", "zlog log trim <log name> <position>" },
          { "fill", "zlog log fill <log name> <position>" },
  };

  if (command.size() > 0 && usages.find(command[0]) == usages.end()) {
    std::cerr << "uknown command \"" << command[0] << "\"" << std::endl;
  }

  if (command.size() == 1 && usages.find(command[0]) != usages.end()) {
    std::cerr << "command requires log name" << std::endl;
  }

  if (command.size() < 2 || usages.find(command[0]) == usages.end()) {
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
    uint64_t tail;
    int ret = log->CheckTail(&tail);
    if (ret != 0) {
      std::cerr << "log::CheckTail " << ret << std::endl;
      return ret;
    }
    if (command.size() == 2 && filename != "") { // append <log name> with input file
      std::ifstream ifs(filename);
      if (!ifs.is_open()) {
        std::cerr << "no such file" << std::endl;
        return 1;
      }
      std::string content( (std::istreambuf_iterator<char>(ifs) ),
                           (std::istreambuf_iterator<char>()    ) );
      int ret = log->Append(content, &tail);
      if (ret != 0) {
        std::cerr << "log::Append " << ret << std::endl;
      }
      return ret;
    } else if (command.size() == 3) { // append <log name> <string>
      int ret = log->Append(command[2], &tail);
      if (ret != 0) {
        std::cerr << "log::Append " << ret << std::endl;
      }
      return ret;
    } else {
      std::cerr << usages.at("append") << std::endl;
      return 1;
    }
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
      switch (ret) {
        case 0:
          break;
        case -ENODATA:
          std::cerr << i << ": invalidated" << std::endl;
          continue;
        case -ERANGE:
          std::cerr << i << ": free" << std::endl;
          continue;
        default:
          std::cerr << "log::Read " << ret << std::endl;
          return ret;
      }
      std::cout << i << ": ";
      for (char c : data.substr(0, 80)) {
        std::cout << std::setfill('0') << std::setw(2) << std::hex << static_cast<int>(c);
      }
      std::cout << std::endl;
    }
    return 0;
  } else if (command[0] == "read") {
    if (command.size() != 3) { // read <log name> <position>
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
    std::string data;
    int ret = log->Read(pos, &data);
    switch (ret) {
      case 0:
        break;
      case -ENODATA:
        std::cerr << "invalidated" << std::endl;
        return ret;
      case -ERANGE:
        std::cerr << "free" << std::endl;
        return ret;
      default:
        std::cerr << "log::Read " << ret << std::endl;
        return ret;
    }
    for (char c : data) {
      std::cout << std::setfill('0') << std::setw(2) << std::hex << static_cast<int>(c);
    }
    std::cout << std::endl;
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
  }

  // Should never reach here, but just to be safe
  std::cerr << "usage:" << std::endl;
  for (const auto &usage : usages) {
    std::cerr << usage.second << std::endl;
  }
  return 1;
}
