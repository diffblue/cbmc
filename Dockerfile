FROM ubuntu:20.04 as builder
ENV DEBIAN_FRONTEND noninteractive
ENV DEBCONF_NONINTERACTIVE_SEEN true
# Timezone data is needed during the installation of dependencies,
# since cmake depends on the tzdata package. In an interactive terminal,
# the user selects the timezone at installation time. Since this needs
# to be a non-interactive terminal, we need to setup some sort of default.
# The UTC one seemed the most suitable one.
RUN echo 'tzdata tzdata/Areas select Etc' | debconf-set-selections; \
    echo 'tzdata tzdata/Zones/Etc select UTC' | debconf-set-selections; \
    apt-get update && apt-get upgrade -y && apt-get install --no-install-recommends -y \
    cmake \
    ninja-build \
    gcc \
    g++ \
    maven \
    flex \
    bison \
    libxml2-utils \
    patch
COPY . /tmp/cbmc
WORKDIR /tmp/cbmc
RUN cmake -S . -Bbuild -G Ninja -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=/usr/bin/gcc -DCMAKE_CXX_COMPILER=/usr/bin/g++ && cd build; ninja -j2

FROM ubuntu:20.04 as runner
COPY --from=builder /tmp/cbmc/build/bin/* /usr/local/bin/
RUN apt-get update && apt-get install -y gcc
