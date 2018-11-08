node {
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
