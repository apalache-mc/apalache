# Third-party libraries

APALACHE requires the following libraries that are not available from
the central Maven repository:

- Box: Available from [GitHub](https://github.com/Kukovec).

In order to download, build and use the above libraries,
execute the following shell command:

```
$ ./install-local.sh
```

The command downloads and compiles the libraries and installs them in your
local Maven cache. Once it is done, you do not have to worry about these
libraries anymore, they will be automatically retrieved by our build system.

Unless you are using `direnv`, as recommended in
[CONTRIBUTING.md](../CONTRIBUTING.md), then add the following line to your
`~/.bashrc` or `~/.zshrc`:

```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$APALACHE/3rdparty
```
