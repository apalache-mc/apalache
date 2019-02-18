FROM maven:3.6.0-jdk-8

RUN apt-get update && apt-get install -y wget \
    g++ \
    binutils \
    make

ADD . /opt/apalache/
WORKDIR /opt/apalache/

# Workaround for Surefire not finding ForkedBooter
# (see https://stackoverflow.com/questions/53010200/maven-surefire-could-not-find-forkedbooter-class)
ENV _JAVA_OPTIONS="-Djdk.net.URLClassPath.disableClassPathURLCheck=true"

RUN "3rdparty/install-local.sh"
ENV LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:/opt/apalache/3rdparty/lib/"

RUN mvn package
CMD ["bin/apalache-mc"]
