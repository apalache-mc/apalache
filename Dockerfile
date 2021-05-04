# NOTE: We build the docker image for Apalache in two phases:
#
# 1. BUILD IMAGE: We use a robust JDK 8 base image to build the package.
# 2. APP IMAGE: We then use a smaller base image, with a different JDK fur
#    execution, and copy over the executable artifacts from the build image.
#
# We use a different base image for two reasons: first, it allows us to provide
# a docker image with a much smaller memory footprint, since we can drop many
# build dependencies; second, JDK 8 is currently necessary for building, but it
# introduces nondetermistic behavior into the Z3 library -- JDK 9+ doesn't have
# this problem.

# 1. BUILD IMAGE
FROM maven:3.6.3-jdk-8-slim AS builder

ADD . /opt/apalache/
WORKDIR /opt/apalache/

# --batch-mode because we are running non-interactive
# skipTests because we check the test in CI, not when packaing the container
RUN mvn --batch-mode -DskipTests package


# 2. APP IMAGE
FROM openjdk:16-slim

# To prepare the app image, we do the following:
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
ENV PATH="/usr/local/openjdk-16/bin/:/opt/apalache/bin:${PATH}"

# TLA parser requires all specification files to be in the same directory
# We assume the user bind-mounted the spec dir into /var/apalache
# In case the directory was not bind-mounted, we create one
RUN mkdir /var/apalache 2>/dev/null

# what to run
ENTRYPOINT ["/opt/apalache/bin/run-in-docker-container"]
