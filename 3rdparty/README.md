Third-party libraries
=====================

APALACHE requires the following libraries that are not available from
the central Maven repository:

 * TLA+2 Tools: tla2tools.jar. Available from:
    [TLA+ Tools page](https://lamport.azurewebsites.net/tla/tools.html "TLA+ Tools").

 * Z3 Java bindings and Z3 shared libraries. The source code is available
 from [Z3 Github page](https://github.com/Z3Prover/z3 "Z3 Github page").
   Check below how one to compile Z3 libraries.

In order to use the required libraries, copy them to the directory `3rdparty`
and execute the following shell command:

```
$ ./install-local.sh
```

The above command will install the both libraries in your local Maven
cache. Once it is done, you do not have to worry about these libraries
anymore, they will be automatically retrieved by our build system.


How to install Z3 libraries
---------------------------

Detailed instructions are available from
 [Z3 webpage](https://github.com/Z3Prover/z3/blob/master/README.md).
If you are using Linux and do not have access to the root account,
the necessary steps are usually like follows:

```
$ git clone https://github.com/Z3Prover/z3.git z3
$ cd z3
$ mkdir $HOME/usr && python scripts/mk_make.py --java -p $HOME/usr/
$ cd build
$ make
$ make install
```

After z3 has been built, add the following line to your ```~/.bashrc```
or ```~/.zshrc```:

```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$HOME/usr/lib
```

Do not forget to copy ```com.microsoft.z3.jar``` to
 ```${APALACHE}/3rdparty```, where ```${APALACHE}``` is the directory
  with the APALACHE source code.