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

# TODO Just use SBT native packager!

# 1. BUILD IMAGE
FROM eclipse-temurin:8-jdk AS builder

ADD . /opt/apalache/
WORKDIR /opt/apalache/

RUN sbt assembly

# 2. APP IMAGE
FROM eclipse-temurin:16-alpine

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
    /opt/apalache/target/scala-2.12/apalache-pkg-*.jar \
    /opt/apalache/target/scala-2.12/
# TODO rm: are packaged in jar?
# Apalache's .tla libraries
# COPY --from=builder \
#     /opt/apalache/src/tla \
#     /opt/apalache/src/tla

# Workaround for Surefire not finding ForkedBooter
# (see https://stackoverflow.com/questions/53010200/maven-surefire-could-not-find-forkedbooter-class)
ENV _JAVA_OPTIONS="-Djdk.net.URLClassPath.disableClassPathURLCheck=true"

# make apalache-mc available in PATH
ENV PATH="/usr/local/openjdk-16/bin/:/opt/apalache/bin:${PATH}"

# TLA parser requires all specification files to be in the same directory
# We assume the user bind-mounted the spec dir into /var/apalache
# In case the directory was not bind-mounted, we create one
RUN mkdir /var/apalache 2>/dev/null

# We need sudo to run apalache using the user (created in the entrypoint script)
RUN apt update && apt install sudo

# what to run
ENTRYPOINT ["/opt/apalache/bin/run-in-docker-container"]
