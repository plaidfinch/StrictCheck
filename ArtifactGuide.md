Artifact for *Keep Your Laziness in Check*

### Using Docker

The artifact is provided as part of a docker image. To investigate the contents
of the artifact, follow these steps:

1. Install Docker following the [official guide](https://docs.docker.com/install/)
2. Download the image [here](https://drive.google.com/file/d/1JPlPobzX32emNHM1h9RiF0ae7Vo5K0Vy/view?usp=sharing); the image is around 3GB in size
3. Check the MD5 hash of the image, it should be: `1382ee411f0bf4dee4448a8e39aa65e6`
4. Run `docker image load -i strictcheck-artifact.tgz`, this may take a few minutes
5. Run `docker images`, and verify it shows an image with `REPOSITORY strictcheck`
6. Run `docker run --rm -it strictcheck`

This will start a shell, and by you can `cd /opt/strictcheck` to investigate the
contents of the library. Running `stack ghci` under `/opt/strictcheck` will
start a `ghci` session with all of StrictCheck's modules loaded.

Note that any changes to the filesystem within the container will be lost when
the you leave the shell. Please refer to the Docker documentation should you
want to persist any modifications within the container.

### Building directly without Docker

If you have `stack` already installed on your system, you may find building from
*StrictCheck* source easier than using docker. Follow these steps for building
from source:

1. Run `git clone https://github.com/kwf/StrictCheck.git`
2. Run `cd StrictCheck/StrictCheck`
3. Run `stack build`
