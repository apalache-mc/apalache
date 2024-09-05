# Building from source

1. Install `git`.
2. Install the [Eclipse Temurin][] or [Zulu][] builds of OpenJDK 17.
   - Apalache currently requires Scala 2.13.8, see [this table of compatible JDK versions][compatibility table].
   - We recommend OpenJDK 17, the latest LTS release.
3. Install [sbt][].
   - On Debian Linux or Ubuntu, [follow this guide](https://www.scala-sbt.org/1.x/docs/Installing-sbt-on-Linux.html#Ubuntu+and+other+Debian-based+distributions)
   - On Arch: `sudo pacman -Syu sbt`
   - On macOS / Homebrew: `brew install sbt`
4. Clone the git repository: `git clone https://github.com/informalsystems/apalache.git`.
5. Change into the project directory: `cd apalache`.
6. Install [direnv][] and run `direnv allow`, or use [another way to set up the shell environment][shell environment].
7. To build and package Apalache for development purposes, run `make`.
   - To skip running the tests, you can run `make package`.
8. To build and package Apalache for releases and end-user distribution, run
   `make dist`.
9. The distribution package will be built to
   `./target/universal/apalache-<VERSION>`, and you can move this wherever you'd
   like, and ensure that the `<dist-package-location>/bin` directory is added to
   your `PATH`.

## Running from within the Apalache repo

If you prefer to keep the built package inside of the Apalache source
repository, you have three options after running `make`:

- Add the `./bin` directory in the source repository to your `PATH`, which will
  make `apalache-mc` available.
- Install [direnv][] and run `direnv allow`, which will put `apalache-mc` in your
  path when you are inside the Apalache repo directory.
- Run `./bin/apalache-mc` directly.


[Eclipse Temurin]: https://adoptium.net/
[Zulu]: https://www.azul.com/downloads/?version=java-17-lts&package=jdk#download-openjdk
[compatibility table]: https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html
[sbt]: https://www.scala-sbt.org/1.x/docs/Setup.html
[direnv]: https://direnv.net/
[shell environment]: https://github.com/informalsystems/apalache/blob/main/CONTRIBUTING.md#environment
