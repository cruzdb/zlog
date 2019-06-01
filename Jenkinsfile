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

tasks["fedora:29:pkg"] = {
  node {
    lock("zlog-build") {
      stage('checkout') {
        checkout scm
      }
      stage('build deps image') {
        sh "BUILD_PKG=yes ci/build_deps_image.sh fedora:29"
      }
      stage('build and test') {
        sh "BUILD_PKG=yes ci/script.sh fedora:29"
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
