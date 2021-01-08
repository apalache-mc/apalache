# Using a docker image

**We publish Docker images for every release** :sunglasses:

[Docker](https://www.docker.com/) lets you to run Apalache in an isolated container.
All dependencies are already installed in docker. However, you have to install docker.

To get the latest Apalache image, issue the command:

```bash
docker pull apalache/mc
```

## Running the docker image

To run an Apalache image, issue the command:

```bash
$ docker run --rm -v <your-spec-directory>:/var/apalache apalache/mc <args>
```

The following docker parameters are used:
- `--rm` to remove the container on exit
- `-v <your-spec-directory>:/var/apalache` bind-mounts `<your-spec-directory>` into
  `/var/apalache` in the container. **This is necessary for
  Apalache to access your specification and the modules it
  extends.**
  From the user perspective, it works as if Apalache was
  executing in `<your-spec-directory>`.
  In particular the tool logs are written in that directory.

  When using SELinux, you might have to use the modified form of `-v` option:
    `-v <your-spec-directory>:/var/apalache:z`
- `apalache/mc` is the APALACHE docker image name. By default, the `latest` stable
  version is used; you can also refer to a specific tool version, e.g., `apalache/mc:0.6.0` or `apalache/mc:unstable`
- `<args>` are the tool arguments as described in [Running the Tool](../running.md).

We provide a convenience wrapper for this docker command in
`script/run-docker.sh`. To run the `latest` image using the script, execute

```bash
$ $APALACHE_HOME/script/run-docker.sh <args>
```

To specify a different image, set `APALACHE_TAG` like so:

```bash
$ APALACHE_TAG=foo $APALACHE_HOME/script/run-docker.sh <args>
```

## Setting an alias

If you are running Apalache on Linux :penguin: or MacOS
:green_apple:, you can define this handy alias in your rc file, which runs
Apalache in docker while sharing the working directory:

```bash

###### using the latest stable

$ alias apalache="docker run --rm -v $(pwd):/var/apalache apalache/mc"

###### using the latest unstable

$ alias apalache="docker run --rm -v $(pwd):/var/apalache apalache/mc:unstable"
```

## Using the unstable version of Apalache

The development of Apalache proceeds at a high pace, and we introduce a
substantial number of improvements in the unstable branch before the next stable
release. Please refer to the [change
log](https://github.com/informalsystems/apalache/blob/unstable/CHANGES.md) and
[manual](https://github.com/informalsystems/apalache/blob/unstable/docs/src/manual.md)
on the unstable branch for the description of the newest features. **We
recommend using the unstable version if you want to try all the exciting new
features of Apalache. But be warned: It is called "unstable" for a reason**. To
use `unstable`, just type `apalache/mc:unstable` instead of `apalache/mc`
everywhere.

Do not forget to pull the docker image from time to time:

```bash
docker pull apalache/mc:unstable
```

Run it with the following command:

```bash
$ docker run --rm -v <your-spec-directory>:/var/apalache apalache/mc:unstable <args>
```

To create an alias pointing to the `unstable` version:

```bash
$ alias apalache="docker run --rm -v $(pwd):/var/apalache apalache/mc:unstable"
```

## Building an image

For an end user there is no need to build an Apalache image. If you like to
produce a modified docker image, take into account that it will take about 30
minutes for the image to get built, due to compilation times of Microsoft Z3. To
build a docker image of Apalache, issue the following command in
`$APALACHE_HOME`:

```bash
$ docker image build -t apalache:0.7.0 .
```


