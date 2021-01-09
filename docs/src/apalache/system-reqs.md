# System requirements

Every commit to [master](https://github.com/informalsystems/apalache) and
[unstable](https://github.com/informalsystems/apalache/tree/unstable) is built
with [GitHub
actions](https://github.com/informalsystems/apalache/actions?query=branch%3Aunstable+workflow%3Abuild)
on MacOS (JDK 1.8.0) and Linux (OpenJDK8). If you would like to run Apalache in
Windows, use a docker image. Check the [Docker
manual](https://docs.docker.com/docker-for-windows/) and the section on [Using
a docker image](./installation/docker.md) for details.

As Apalache is using Microsoft Z3 as a backend SMT solver, the required memory
largely depends on Z3. We recommend to allocate at least 4GB of memory for the
tool.
