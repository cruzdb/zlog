#include <iostream>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "internal.hpp"

namespace po = boost::program_options;

int main(int argc, char **argv)
{
  std::string pool;
  std::string log_name;
  std::string server;
  std::string port;
  int width;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&log_name)->required(), "Log name")
    ("create-cut", po::bool_switch()->default_value(false), "Create a cut")
    ("set-width", po::value<int>(&width)->default_value(-1), "Set stripe width")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  // connect
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  cluster.conf_parse_env(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  zlog::SeqrClient *client = NULL;
  //client = new zlog::SeqrClient(server.c_str(), port.c_str());
  //client->Connect();

  zlog::LogLL log;
  ret = zlog::LogLL::Open(ioctx, log_name, client, log);
  assert(ret == 0);

  if (width != -1) {
    if (width > 0) {
      ret = log.SetStripeWidth(width);
      if (ret)
        std::cerr << "set-width: failed to set width " << width
          << " ret " << ret << std::endl;
      else
        std::cout << "set-width: set log stripe width " << width << std::endl;
    } else
      std::cerr << "set-width: invalid stripe width " << width << std::endl;
  } else if (vm["create-cut"].as<bool>()) {
    uint64_t epoch, maxpos;
    ret = log.CreateCut(&epoch, &maxpos);
    if (ret)
      std::cerr << "create-cut: failed ret " << ret << std::endl;
    else
      std::cout << "create-cut: log " << log_name << " e" << epoch
        << " max_pos " << maxpos << std::endl;
  }

  ioctx.close();
  cluster.shutdown();

  return 0;
}
