# Installation

There are three ways to run Apalache:

  1. [Prebuilt package](./jvm.md): download a prebuilt package and run it in the JVM.
  2. [Docker](./docker.md): download and run a Docker image.
  3. [Build from source](./source.md): build Apalache from sources and run the compiled package.

If you just want to try the tool, we recommend using the [prebuilt package](./jvm.md).

## System requirements

**Memory**: Apalache uses a backend SMT solver, Microsoft Z3 by default, and the
required memory largely depends on the selected solver and specification. We
recommend to allocate at least 4GB of memory for the tool.
