# Prebuilt Packages

You need to download and install a Java Virtual Machine first. Apalache requires Java 25. We recommend
the [Eclipse Temurin][] or [Zulu][] builds of OpenJDK.

Once you have installed Java, download the [latest
release](https://github.com/apalache-mc/apalache/releases) and unpack into
a directory of your choice. Depending on your OS, you have two options.

*Option 1: Linux, macOS.* You can run the script `./bin/apalache-mc`, or,
better, add the `./bin` directory to your `PATH` and run `apalache-mc`.

*Option 2: Windows.* You can run the script `./bin/apalache-mc.bat`

Alternatively, you can run Java directly with

```
java --sun-misc-unsafe-memory-access=allow -jar ./lib/apalache.jar <args>
```

The packaged launch scripts supply this Java 25 compatibility option automatically.

The arguments `<args>` are explained in [Running the Tool](../running.md).

[Eclipse Temurin]: https://adoptium.net/
[Zulu]: https://www.azul.com/downloads/?version=java-25-lts&package=jdk#download-openjdk
