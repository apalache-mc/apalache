To install the APALACHE project, you have to do the following:

 1. Install [Oracle JDK8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
 1. Install [Apache Maven](https://maven.apache.org/)
 1. Run the script `./3rdparty/install-local.sh`, which will download
    and install TLA+ Tools and Microsoft Z3.
 1. Run `mvn package`, which will compile the project, run tests
    and assemble the package.

If all these steps were successful, you can run the model checker as explained
in [README](./README.md).

