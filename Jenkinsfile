def images = ["ubuntu:bionic", "ubuntu:xenial", "debian:stretch", "fedora:29", "centos:7"]
def tasks = [:]

images.each { image ->
  tasks["${image}"] = {
    node {
      lock("zlog-build") {
	stage('checkout') {
	  checkout scm
	}
        stage('build deps image') {
          sh "ci/build_deps_image.sh ${image}"
        }
        stage('build and test') {
          sh "ci/script.sh ${image}"
        }
      }
    }
  }
}

//for (int i = 0; i < images.size(); i++) {
//  tasks["${images[i]}"] = {
//    node {
//      lock("zlog-build") {
//        stage('checkout') {
//          checkout scm
//        }
//        stage('build deps image') {
//          sh "ci/build_deps_image.sh ${images[i]}"
//        }
//        stage('build and test') {
//          sh "ci/script.sh ${images[i]}"
//        }
//      }
//    }
//  }
//}

stage("matrix") {
  parallel tasks
}
