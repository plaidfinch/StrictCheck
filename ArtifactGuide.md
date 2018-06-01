Artifact for *Keep Your Laziness in Check*

### Building directly without Docker

If you have `stack` already installed on your system, you may find building from
*StrictCheck* source easier than using docker. Follow these steps for building
from source:

1. Run `git clone https://github.com/kwf/StrictCheck.git`
2. Run `cd StrictCheck/StrictCheck`
3. Run `stack build`

### Using Docker

The artifact is provided as part of a docker image. To investigate the contents
of the artifact, follow these steps:

1. Install Docker following the [official guide](https://docs.docker.com/install/)
2. Download the image [here](https://drive.google.com/file/d/1JPlPobzX32emNHM1h9RiF0ae7Vo5K0Vy/view?usp=sharing); the image is around 3GB in size
3. Start the docker daemon, docker may ask for your host system credentials (it
may also show a login UI for dockerhub, but you don't need to login to
dockerhub for these instructions)
4. Run `docker image load -i strictcheck-artifact.tgz`, this may take a few minutes
5. Run `docker images`, and verify it shows an image with `REPOSITORY strictcheck`
6. Run `docker run --rm -it strictcheck`

This will start a shell, and you can `cd /opt/strictcheck` to investigate the
contents of the library. Running `stack ghci` under `/opt/strictcheck` will
start a `ghci` session with all of StrictCheck's modules loaded.

Note that any changes to the filesystem within the container will be lost when
the you leave the shell. Please refer to the Docker documentation should you
want to persist any modifications within the container.

### Step-by-Step guide

To test the specifications described in the paper, start a `ghci` shell that
loads all of StrictCheck's modules by following one of the two approaches
described above.

The `Test.StrictCheck.Examples.List` module contains all of the specifications
we showcased in the paper. To invoke StrictCheck with, for example, the
`take_spec`, use these commands:

```
ghci> strictCheckSpecExact take_spec (take @Int)
+++ OK, passed 100 tests.
```

You can use `strictCheckSpecExact` with all of the `_spec` functions from this
module, this will start the randomized testing of the given specification. We
have also included a few incorrect specifications in this module, and you can
test them to verify StrictCheck can indeed catch incorrect specifications.

To run all of these tests at once, you can simply run `stack test`.

### How to access haddock documentation

If you used to the docker image to review StrictCheck, run the following
commands to copy the generated haddock documentation to a location on your host
system:

```
id=$(docker create strictcheck)
docker cp $id:path /path/to/host/system
docker rm -v $id
```

If you built StrictCheck directly without using docker, then run `stack haddock`
in the StrictCheck source directory, `stack` will output a location to the
documentaion html files like the following for local packages:

```
/path/to/StrictCheck/.stack-work/install/x86_64-osx/lts-11.10/8.2.2/doc/index.html
```

Then, you can open the `index.html` file with a web browser of your choice.

### How to build the docker image

Run the following commands:

```
git clone https://github.com/kwf/StrictCheck.git
cd StrictCheck/StrictCheck
docker build -t strictcheck:latest --squash .
docker save strictcheck | gzip -9 > strictcheck-artifact.tgz
```
