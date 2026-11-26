FROM docker.m.daocloud.io/jenkins/jenkins@sha256:4d85f6cf5a8939647921564952d12a5a761f32a3bc520c2f4e5c3cafa7ea660f
ARG JENKINS_UC_DOWNLOAD=https://mirrors.aliyun.com/jenkins
COPY --chown=jenkins:jenkins plugins.lock.txt /usr/share/jenkins/ref/plugins.lock.txt
RUN jenkins-plugin-cli --latest=false --plugin-file /usr/share/jenkins/ref/plugins.lock.txt
