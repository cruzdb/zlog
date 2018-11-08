def images = ["ubuntu:bionic", "fedora:29"]
def tasks = [:]

for (int i = 0; i < images.size(); i++) {
  tasks["${images[i]}"] = {
    node {
      lock("zlog-build") {
        stage('checkout') {
          checkout scm
        }
        stage('build deps image') {
          sh "ci/build_deps_image.sh ubuntu:bionic"
        }
        stage('build and test') {
          sh "ci/script.sh ubuntu:bionic"
        }
      }
    }
  }
}

stage("matrix") {
  parallel tasks
}
