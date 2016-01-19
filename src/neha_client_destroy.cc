#include <cerrno>
#include <deque>
#include <iostream>
#include <rados/librados.hpp>
#include <rados/librados.h>
#include <gtest/gtest.h>
#include "libzlog.hpp"
#include "libzlog.h"

std::string get_temp_pool_name()                                                
{                                                                               
  char hostname[80];                                                            
  char out[80];                                                                 
  memset(hostname, 0, sizeof(hostname));                                        
  memset(out, 0, sizeof(out));                                                  
  gethostname(hostname, sizeof(hostname)-1);                                    
  static int num = 1;                                                           
  sprintf(out, "%s-%d-%d", hostname, getpid(), num);                            
  num++;                                                                        
  std::string prefix("test-rados-api-");                                        
  prefix += out;                                                                
  return prefix;                                                                
}

int create_one_pool_pp(const std::string &pool_name, rados_t *rados)            
{                                                                               
  int ret = rados_create(rados, NULL);                                          
  if (ret)                                                                      
    return ret;                                                                 
  ret = rados_conf_read_file(*rados, NULL);                                     
  if (ret)                                                                      
    return ret;                                                                 
  ret = rados_conf_parse_env(*rados, NULL);                                     
  if (ret)                                                                      
    return ret;                                                                 
  ret = rados_connect(*rados);                                                  
  if (ret)                                                                      
    return ret;                                                                 
  ret = rados_pool_create(*rados, pool_name.c_str());                           
  if (ret)                                                                      
    return ret;                                                                 
  return 0;                                                                     
}                                                                               
                                                                                
int destroy_one_pool_pp(const std::string &pool_name, rados_t rados)            
{                                                                               
  int ret = rados_pool_delete(rados, pool_name.c_str());                        
  if (ret) {                                                                    
    rados_shutdown(rados);                                                      
    return ret;                                                                 
  }                                                                             
  rados_shutdown(rados);                                                        
  return 0;                                                                     
}       

std::string create_one_pool_pp(const std::string &pool_name,
                               librados::Rados &cluster)
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
  ret = cluster.connect();                                                      
  if (ret) {                                                                    
    cluster.shutdown();                                                         
    std::ostringstream oss;                                                     
    oss << "cluster.connect failed with error " << ret;                         
    return oss.str();                                                           
  } 
  return "";                                                                            
}                                                                               
                                                                                
/*                                                                              
 * Helper function from ceph/src/test/librados/test.cc                          
 */                                                                             
int destroy_one_pool_pp(const std::string &pool_name, librados::Rados &cluster) 
{                                                                               
  int ret = cluster.pool_delete(pool_name.c_str());                             
  if (ret) {                                                                    
    cluster.shutdown();                                                         
    return ret;                                                                 
  }          
  cluster.shutdown();                                                           
  return 0;                                                                     
}

void my_driver_function()
{
  // Creating a Rados pool.
	librados::Rados rados;
	std::string pool_name = "pool_1234";
	assert(""==create_one_pool_pp(pool_name, rados));

  assert(destroy_one_pool_pp(pool_name, rados) == 0);
}                  
int main()
{
  my_driver_function();
  return 0;
}
