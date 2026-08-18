# Prebuilt Packages

You need to download and install a Java Virtual Machine first. We recommend running Apalache on Java 25, using the
[Eclipse Temurin][] or [Zulu][] builds of OpenJDK. Released artifacts maintain bytecode compatibility with Java 21 and
should run on Java 21 or newer, but Java 21 is less thoroughly tested than the recommended Java 25 runtime.

Once you have installed Java, download the [latest
release](https://github.com/apalache-mc/apalache/releases) and unpack into
a directory of your choice. Depending on your OS, you have two options.

*Option 1: Linux, macOS.* You can run the script `./bin/apalache-mc`, or,
better, add the `./bin` directory to your `PATH` and run `apalache-mc`.

*Option 2: Windows.* You can run the script `./bin/apalache-mc.bat`

Alternatively, you can run Java directly with

```
java -jar ./lib/apalache.jar <args>
```

The arguments `<args>` are explained in [Running the Tool](../running.md).

[Eclipse Temurin]: https://adoptium.net/
[Zulu]: https://www.azul.com/downloads/?version=java-25-lts&package=jdk#download-openjdk
