# Using a docker image

**We publish Docker images for every release** :sunglasses:

**NOTE**: Running Apalache through a docker application image complicates
configuration of the tool considerably. Unless you have a pressing need to use
the docker image, we recommend using one of our [prebuilt releases](./jvm.md).

[Docker](https://www.docker.com/) lets you run the Apalache tool from inside
an isolated container. The only dependency required to run Apalache is a
suitable JVM, and the container supplies this. However, you must already have
[docker installed](https://docs.docker.com/get-docker/).

To get the latest Apalache image, issue the command:

```bash
docker pull ghcr.io/apalache-mc/apalache
```

## Running the docker image

To run an Apalache image, issue the command:

```bash
$ docker run --rm -v <your-spec-directory>:/var/apalache ghcr.io/apalache-mc/apalache <args>
```

The following docker parameters are used:

- `--rm` to remove the container on exit
- `-v <your-spec-directory>:/var/apalache` bind-mounts `<your-spec-directory>` into
  `/var/apalache` in the container. **This is necessary for
  Apalache to access your specification and the modules it
  extends.**
  From the user perspective, it works as if Apalache was
  executing in `<your-spec-directory>`.
  In particular, the tool logs are written in that directory.

  When using SELinux, you might have to use the modified form of `-v` option:
    `-v <your-spec-directory>:/var/apalache:z`
- `apalache-mc/apalache` is the APALACHE docker image name. By default, the `latest` stable
  version is used; you can also refer to a specific tool version, e.g., `apalache-mc/apalache:0.6.0` or `apalache-mc/apalache:main`
- `<args>` are the tool arguments as described in [Running the Tool](../running.md).

We provide a convenience wrapper for this docker command in
`script/run-docker.sh`. Assuming you've downloaded the Apalache source code into
a directory located at `APALACHE_HOME`, you can run the `latest` image via the
script by running:

```bash
$ $APALACHE_HOME/script/run-docker.sh <args>
```

To specify a different image, set `APALACHE_TAG` like so:

```bash
$ APALACHE_TAG=foo $APALACHE_HOME/script/run-docker.sh <args>
```

## Setting an alias

If you are running Apalache on Linux :penguin: or macOS
:green_apple:, you can define this handy alias in your rc file, which runs
Apalache in docker while sharing the working directory:

```bash

###### using the latest stable

$ alias apalache='docker run --rm -v $(pwd):/var/apalache ghcr.io/apalache-mc/apalache'

###### using the latest main

$ alias apalache='docker run --rm -v $(pwd):/var/apalache ghcr.io/apalache-mc/apalache:main'
```

## Using the development branch of Apalache

The development of Apalache proceeds at a quick pace, and we cut releases weekly.
Please refer to the [changelog][] and the [manual][] on the `main` development
branch for a report of the newest features. Since we cut releases weekly, you
should have access to all the latest features in the last week by using the
`latest` tag. However, if you wish to use the very latest developments as they
are added throughout the week, you can run the image with the `main` tag: just
type `ghcr.io/apalache-mc/apalache:main` instead of
`ghcr.io/apalache-mc/apalache` everywhere.

Do not forget to pull the docker image from time to time:

```bash
docker pull ghcr.io/apalache-mc/apalache:main
```

Run it with the following command:

```bash
$ docker run --rm -v <your-spec-directory>:/var/apalache ghcr.io/apalache-mc/apalache:main <args>
```

To create an alias pointing to the `main` version:

```bash
$ alias apalache='docker run --rm -v $(pwd):/var/apalache ghcr.io/apalache-mc/apalache:main'
```

[changelog]: https://github.com/apalache-mc/apalache/blob/main/CHANGES.md
[manual]: https://github.com/apalache-mc/apalache/blob/main/docs/src/apalache/index.md


## Building an image

For an end user, there is no need to build an Apalache image. If you like to
produce a modified docker image, take into account that it will take about 30
minutes for the image to get built, due to compilation times of Microsoft Z3. To
build a docker image of Apalache, issue the following command in
`$APALACHE_HOME`:

```bash
$ docker image build -t apalache:0.7.0 .
```


