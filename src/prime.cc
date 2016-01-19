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
  ret =cluster.pool_lookup(pool_name.c_str()); 
  // temp hack;
  return "";                                                                           
  ret = cluster.pool_create(pool_name.c_str());                                 
  if (ret) {                                                                    
    cluster.shutdown();                                                         
    std::ostringstream oss;                                                     
    oss << "cluster.pool_create(" << pool_name << ") failed with error " << ret;
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

	// Associating the rados pool to an ioctx
	librados::IoCtx ioctx;
	// c_str returns a c type string(char*). It is a function of the string
	// object
	assert(rados.ioctx_create(pool_name.c_str(), ioctx) == 0);

	// Creating sequencer client object
	zlog::SeqrClient client("localhost", "5678");
	client.Connect();

	// Create a log
	zlog::Log log;

	int ret = zlog::Log::Open(ioctx, "new_log", &client, log);

        std::cout << "Log opened " << ret << "\n";

        uint64_t tail;                                                                
	ret = log.CheckTail(&tail, false);
        assert(ret == 0);
	// Append message 1 to log
	ceph::bufferlist m[100];
        for (int i = 0; i < 100; i++)
        {
	  m[i].append("prime" + std::to_string(i));
	  uint64_t pos1;
	  ret = log.Append(m[i], &pos1);
	  assert(ret == 0);

          std::cout << "position " << pos1 << "\n" << std::flush;
        }
	// Append message 2 to log
	ceph::bufferlist m2[100];
	for (int i=100; i< 200; i++)
        {
		m2[i-100].append("prime" + std::to_string(i));
		uint64_t pos2;
		ret = log.Append(m2[i-100], &pos2);
		assert(ret == 0);
        
                std::cout << "position " << pos2 << "\n" << std::flush;
        }

  //assert(destroy_one_pool_pp(pool_name, rados) == 0);
}                  
int main()
{
  my_driver_function();
  return 0;
}
