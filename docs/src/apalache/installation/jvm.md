# Prebuilt Packages

You need to download and install a Java Virtual Machine first. 
We recommend version 17 of the [Eclipse Temurin][] or [Zulu][] builds of OpenJDK.

Once you have installed Java, download the [latest
release](https://github.com/informalsystems/apalache/releases) and unpack into
a directory of your choice. Depending on your OS, you have two options.

*Option 1: Linux, macOS.* You can run the script `./bin/apalache-mc`, or,
better, add the `./bin` directory to your `PATH` and run `apalache-mc`.

*Option 2: Windows.* You have to run Java directly with

  ```
  java.exe -jar ./lib/apalache.jar <args>
  ```

  The arguments `<args>` are explained in [Running the Tool](../running.md).

If you would like to contribute a command-line script for running Apalache in
Windows, please [open a pull
request](https://github.com/informalsystems/apalache/blob/main/CONTRIBUTING.md#making-a-pull-request).

[Eclipse Temurin]: https://adoptium.net/
[Zulu]: https://www.azul.com/downloads/?version=java-17-lts&package=jdk#download-openjdk
