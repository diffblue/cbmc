# syntax=docker/dockerfile:1
FROM ubuntu:24.04 AS builder
ENV DEBIAN_FRONTEND=noninteractive
ENV DEBCONF_NONINTERACTIVE_SEEN=true
# Timezone data is needed during the installation of dependencies,
# since cmake depends on the tzdata package. In an interactive terminal,
# the user selects the timezone at installation time. Since this needs
# to be a non-interactive terminal, we need to setup some sort of default.
# The UTC one seemed the most suitable one.
#
# The apt cache mounts (with docker-clean removed so downloaded packages are
# kept) let the package downloads persist across CI builds via the buildx
# cache, rather than being re-fetched every time.
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    rm -f /etc/apt/apt.conf.d/docker-clean && \
    echo 'Binary::apt::APT::Keep-Downloaded-Packages "true";' \
      > /etc/apt/apt.conf.d/keep-cache && \
    echo 'tzdata tzdata/Areas select Etc' | debconf-set-selections && \
    echo 'tzdata tzdata/Zones/Etc select UTC' | debconf-set-selections && \
    apt-get update && apt-get upgrade -y && \
    apt-get install --no-install-recommends -y \
    cmake \
    make \
    ninja-build \
    ccache \
    gcc \
    g++ \
    maven \
    flex \
    bison \
    libxml2-utils \
    patch
COPY . /tmp/cbmc
WORKDIR /tmp/cbmc
# Build through ccache, storing its objects in a buildx cache mount.  CBMC's
# CMakeLists.txt already enables ccache automatically (RULE_LAUNCH_COMPILE) when
# it finds the ccache program, so we only need ccache installed and CCACHE_DIR
# pointed at the mount -- adding -DCMAKE_*_COMPILER_LAUNCHER here as well would
# stack a second ccache and fail with "Recursive invocation".  Unlike Docker
# layer caching -- which is invalidated by the `COPY . /tmp/cbmc` above whenever
# any source file changes -- ccache keys on preprocessed compiler input, so the
# cache survives source changes and most objects are reused.  The mount is
# persisted across CI runs by the buildkit-cache-dance step in the workflow.
#
# gcc/g++ are reinstalled from apt on every build, so their mtimes differ
# run-to-run; CCACHE_COMPILERCHECK=content keys on the compiler's hash instead
# so an identical-but-reinstalled toolchain still hits.  CCACHE_MAXSIZE bounds
# the persisted cache, and the surrounding `ccache -z`/`ccache -s` print the
# hit rate to the build log.
RUN --mount=type=cache,target=/ccache \
    export CCACHE_DIR=/ccache CCACHE_COMPILERCHECK=content CCACHE_MAXSIZE=500M && \
    cmake -S . -Bbuild -G Ninja -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=/usr/bin/gcc -DCMAKE_CXX_COMPILER=/usr/bin/g++ && \
    ccache -z && \
    ninja -C build -j2 && \
    ccache -s

FROM ubuntu:24.04 AS runner
COPY --from=builder /tmp/cbmc/build/bin/* /usr/local/bin/
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    apt-get update && apt-get install -y gcc
