# Building from source

1. Install `git`.
2. Install [OpenJDK8][] or [Zulu JDK8][].
   - Apalache currently requires Scala 12.0 so **you must install version 8 of
     Java, otherwise Scala will not compile!** See the [compatibility table][].
3. Install [Apache Maven][].
   - On Debian Linux or Ubuntu: `sudo apt-get install maven`.
   - On Arch: `sudo pacman -Syu maven`
4. Clone the git repository: `git clone https://github.com/informalsystems/apalache.git`.
5. Change into the project directory: `cd apalache`.
7. Run `make`.
6. *Optionally* install [direnv][] and run `direnv allow`
8. Confirm you can run the executable. It should print the inline CLI help message.
   - If you used `direnv`, then `apalache-mc` will be in your path.
   - Otherwise, run `./bin/apalache-mc`.


[OpenJDK8]: https://openjdk.java.net/install/
[Zulu JDK8]: https://www.azul.com/downloads/zulu-community/?version=java-8-lts&architecture=x86-64-bit&package=jdk
[compatibility table]: https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html
[Apache Maven]: https://maven.apache.org/
[direnv]: https://direnv.net/
