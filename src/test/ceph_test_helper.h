#pragma once

static std::string get_temp_pool_name(const std::string &prefix = "test-rados-api-")
{
  char hostname[80];
  char out[160];
  memset(hostname, 0, sizeof(hostname));
  memset(out, 0, sizeof(out));
  gethostname(hostname, sizeof(hostname)-1);
  static int num = 1;
  snprintf(out, sizeof(out), "%s-%d-%d", hostname, getpid(), num);
  num++;
  return prefix + out;
}

static std::string connect_cluster_pp(librados::Rados &cluster,
                               const std::map<std::string, std::string> &config)
{
  char *id = getenv("CEPH_CLIENT_ID");
  if (id) std::cerr << "Client id is: " << id << std::endl;

  int ret;
  ret = cluster.init(id);
  if (ret) {
    std::ostringstream oss;
    oss << "cluster.init failed with error " << ret;
    return oss.str();
  }
  ret = cluster.conf_read_file(NULL);
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.conf_read_file failed with error " << ret;
    return oss.str();
  }
  cluster.conf_parse_env(NULL);

  for (auto &setting : config) {
    ret = cluster.conf_set(setting.first.c_str(), setting.second.c_str());
    if (ret) {
      std::ostringstream oss;
      oss << "failed to set config value " << setting.first << " to '"
          << setting.second << "': " << ret;
      return oss.str();
    }
  }

  ret = cluster.connect();
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.connect failed with error " << ret;
    return oss.str();
  }
  return "";
}

static std::string create_one_pool_pp(const std::string &pool_name, librados::Rados &cluster,
                               const std::map<std::string, std::string> &config)
{
  std::string err = connect_cluster_pp(cluster, {});
  if (err.length())
    return err;
  int ret = cluster.pool_create(pool_name.c_str());
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.pool_create(" << pool_name << ") failed with error " << ret;
    return oss.str();
  }
  return "";
}

static std::string create_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
{
    return create_one_pool_pp(pool_name, cluster, {});
}

static int destroy_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
{
  int ret = cluster.pool_delete(pool_name.c_str());
  if (ret) {
    cluster.shutdown();
    return ret;
  }
  cluster.shutdown();
  return 0;
}

