FROM fedora:26

RUN dnf install -y sudo fedora-packager rpmdevtools mock mock-scm

RUN adduser -m -s /bin/bash user && usermod -a -G mock user
RUN echo "user ALL=(root) NOPASSWD:ALL" > /etc/sudoers.d/user \
  && chmod 0440 /etc/sudoers.d/user

USER user
WORKDIR /home/user
