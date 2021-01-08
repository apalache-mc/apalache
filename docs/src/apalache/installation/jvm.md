# Running in Java Virtual Machine

You have to download and install a Java Virtual Machine first. For instance,
[OpenJDK](https://openjdk.java.net/) should work (we tried Apalache with OpenJDK 11).

Once you have installed Java, download the [latest
release](https://github.com/informalsystems/apalache/releases) and unpack into
a directory of your choice. Depending on your OS, you have two options.

*Option 1: Linux, MacOS.* You can run the script `./bin/apalache-mc`. It is
that simple.

*Option 2: Windows.* You have to run Java directly:

  - Check the application name in the directory `mod-distribution\target`.
    It should be called `apalache-pkg-X.Y.Z-RELEASE-full.jar`, where `X.Y.Z`
    is the release number, for instance, 0.8.0.

  - Run Java as follows:

  ```
  java.exe -cp mod-distribution\target\apalache-pkg-X.Y.Z-RELEASE-full.jar <args>
  ```

  The arguments `<args>` are explained in [Running the Tool](../running.md).

If you would like to contribute a command-line script for running Apalache in
Windows, please [open a pull
request](https://github.com/informalsystems/apalache/blob/unstable/CONTRIBUTING.md#making-a-pull-request).
