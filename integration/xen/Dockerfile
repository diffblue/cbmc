FROM ubuntu:16.04

RUN apt-get update && apt-get --no-install-recommends -y install \
        build-essential gcc git make flex bison \
        software-properties-common libwww-perl python \
        bin86 gdb bcc liblzma-dev python-dev gettext iasl \
        uuid-dev libncurses5-dev libncursesw5-dev pkg-config \
        libgtk2.0-dev libyajl-dev sudo time

ADD integration/xen/docker_compile_xen.sh docker_compile_xen.sh
ADD src /tmp/cbmc/src
ADD scripts /tmp/cbmc/scripts
RUN ./docker_compile_xen.sh
VOLUME /tmp/cbmc
VOLUME /tmp/xen_compilation
