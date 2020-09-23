FROM maven:3.6.3-jdk-8-slim AS builder

# This is the image for building apalache itself

ADD . /opt/apalache/
WORKDIR /opt/apalache/

# --batch-mode because we are running non-interactive
# skipTests because we check the test in CI, not when packaing the container
RUN mvn --batch-mode -DskipTests package

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

# make apalache-mc available in PATH
ENV PATH="/usr/local/openjdk-8/bin/:/opt/apalache/bin:${PATH}"

# TLA parser requires all specification files to be in the same directory
# We assume the user bind-mounted the spec dir into /var/apalache
# In case the directory was not bind-mounted, we create one
RUN mkdir /var/apalache 2>/dev/null

# what to run
ENTRYPOINT ["/opt/apalache/bin/run-in-docker-container"]
