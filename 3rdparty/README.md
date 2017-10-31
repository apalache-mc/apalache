Third-party libraries
=====================

APALACHE requires the following libraries that are not available from
the central Maven repository:

 * TLA+2 Tools: tla2tools.jar. Available from:
    [TLA+ Tools page](https://lamport.azurewebsites.net/tla/tools.html "TLA+ Tools").

 * Z3 Java bindings and Z3 shared libraries. The source code is available
 from [Z3 Github page](https://github.com/Z3Prover/z3 "Z3 Github page").
   Check below how one to compile Z3 libraries.

In order to download, build and use the above libraries,
execute the following shell command:

```
$ ./install-local.sh
```

The above command downloads and compiles z3, downloads TLA2Tools and
installs the both libraries in your local Maven
cache. Once it is done, you do not have to worry about these libraries
anymore, they will be automatically retrieved by our build system.

After the command has finished, add the following line to
your ```~/.bashrc``` or ```~/.zshrc```:

```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$APALACHE/3rdparty
```

(The above command is needed to load the Z3 shared libraries.)
