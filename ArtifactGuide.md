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
3. Check the MD5 hash of the image, it should be: `37a0dc0185614989a8e6cacd2e1026a9`
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

### How to build the docker image

Run the following commands:

```
git clone https://github.com/kwf/StrictCheck.git
cd StrictCheck/StrictCheck
docker build -t strictcheck:latest --squash .
docker save strictcheck | gzip -9 > strictcheck-artifact.tgz
```
