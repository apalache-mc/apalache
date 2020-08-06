FROM maven:3.6.3-jdk-8-slim AS thirdparty
# This is image for building vendored dependencies
#
# We build the vendored dependencies in their own image so we only need to
# rebuild this image when those dependencies change, and so we don't need to
# keep their build dependencies.

RUN apt-get update && apt-get install -y wget \
    g++ \
    binutils \
    make \
    git \
    python

ADD ./3rdparty /opt/apalache/3rdparty
WORKDIR /opt/apalache/

# Workaround for Surefire not finding ForkedBooter
# (see https://stackoverflow.com/questions/53010200/maven-surefire-could-not-find-forkedbooter-class)
ENV _JAVA_OPTIONS="-Djdk.net.URLClassPath.disableClassPathURLCheck=true"

RUN 3rdparty/install-local.sh --nocache

FROM maven:3.6.3-jdk-8-slim AS builder

# This is the image for building apalache itself

ADD . /opt/apalache/
WORKDIR /opt/apalache/

# Vendored binaries
COPY --from=thirdparty /opt/apalache/3rdparty/bin /opt/apalache/3rdparty/bin
# Vendored libraies
COPY --from=thirdparty /opt/apalache/3rdparty/lib /opt/apalache/3rdparty/lib
# The maven repository
COPY --from=thirdparty /root/.m2 /root/.m2

# Workaround for Surefire not finding ForkedBooter
# (see https://stackoverflow.com/questions/53010200/maven-surefire-could-not-find-forkedbooter-class)
ENV _JAVA_OPTIONS="-Djdk.net.URLClassPath.disableClassPathURLCheck=true"

ENV LD_LIBRARY_PATH="/opt/apalache/3rdparty/lib/:${LD_LIBRARY_PATH}"

# clean the leftovers from the previous non-docker builds and build the package
RUN mvn clean package

FROM openjdk:8-slim

# This is the app image
#
# To prepare it, we
#
# - copy over all the artifacts needed to run
# - prepare the enviroment
# - declare the entrypoint

WORKDIR /opt/apalache/

COPY --from=builder \
    /opt/apalache/LICENSE \
    /opt/apalache/LICENSE
# Vendored binaries
COPY --from=builder \
    /opt/apalache/3rdparty/bin/ \
    /opt/apalache/3rdparty/bin/
# Vendored libraries
COPY --from=builder \
    /opt/apalache/3rdparty/lib/ \
    /opt/apalache/3rdparty/lib/
# Executable script entrypoints
COPY --from=builder \
    /opt/apalache/bin/ \
    /opt/apalache/bin/
# Workaround for broken docker behavior on staged builds with multiple COPY commands
# see https://github.com/moby/moby/issues/37965#issuecomment-426853382
RUN true
# The jars
COPY --from=builder \
    /opt/apalache/mod-distribution/target/apalache-pkg-*.jar \
    /opt/apalache/mod-distribution/target/
# Apalache's .tla libraries
COPY --from=builder \
    /opt/apalache/src/tla \
    /opt/apalache/src/tla

# Workaround for Surefire not finding ForkedBooter
# (see https://stackoverflow.com/questions/53010200/maven-surefire-could-not-find-forkedbooter-class)
ENV _JAVA_OPTIONS="-Djdk.net.URLClassPath.disableClassPathURLCheck=true"

ENV LD_LIBRARY_PATH="/opt/apalache/3rdparty/lib/:${LD_LIBRARY_PATH}"

# make apalache-mc available in PATH
ENV PATH="/usr/local/openjdk-8/bin/:/opt/apalache/bin:${PATH}"

# TLA parser requires all specification files to be in the same directory
# We assume the user bind-mounted the spec dir into /var/apalache
# In case the directory was not bind-mounted, we create one
RUN mkdir /var/apalache 2>/dev/null

# what to run
ENTRYPOINT ["/opt/apalache/bin/run-in-docker-container"]
