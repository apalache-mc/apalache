# Building from source

1. Install `git`.
2. Install [OpenJDK8][] or [Zulu JDK8][].
   - Apalache currently requires Scala 12.0 so **you must install version 8 of
     Java, otherwise Scala will not compile!** See the [compatibility table][].
3. Install [sbt][].
   - On Debian Linux or Ubuntu, [follow this guide](https://www.scala-sbt.org/1.x/docs/Installing-sbt-on-Linux.html#Ubuntu+and+other+Debian-based+distributions)
   - On Arch: `sudo pacman -Syu sbt`
   - On macOS / Homebrew: `brew install sbt`
4. Clone the git repository: `git clone https://github.com/informalsystems/apalache.git`.
5. Change into the project directory: `cd apalache`.
7. Run `make`.
   - To skip running the tests, you can run `make package`
8. The distribution package will be built to `./target/universal/apalache-<VERSION>`, and you can
   move this wherever you'd like, and ensure that the `<dist-package-location>/bin` directory
   is added to your `PATH`.

## Running from within the Apalache repo

If you prefer to keep the built package inside of the Apalache source
repository, you have three options after running `make`:

- Add the `./bin` directory in the source repository to your `PATH`, which will
  make `apalche-mc` available.
- Install [direnv][] and run `direnv allow`, which will put `apalche-mc` in your
  path when you are inside of the Apalache repo directory.
- Run `./bin/apalache-mc` directly.


[OpenJDK8]: https://openjdk.java.net/install/
[Zulu JDK8]: https://www.azul.com/downloads/zulu-community/?version=java-8-lts&architecture=x86-64-bit&package=jdk
[compatibility table]: https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html
[sbt]: https://www.scala-sbt.org/1.x/docs/Setup.html
[direnv]: https://direnv.net/
