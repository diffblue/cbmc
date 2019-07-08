#!/usr/bin/env bash
#
# Copyright Norbert Manthey, 2019

# Run commands inside container
#
# Usage:
# ./scripts/run_in_container "<path>/Dockerfile" command with args
#
# In case the environment variable CONTAINER is set already, the value of that
# variable will be used as the image to use. Otherwise, the provided Dockerfile
# will be used to create the image to be used in this script.

set -ex
DOCKERFILE="$1"  # Dockerfile
shift

USER_FLAGS="-e USER="$(id -u)" -u=$(id -u)"

# disable getting the source again
if [ -z "$1" ] || [ "$1" = "sudo" ]
then
	USER_FLAGS=""
	shift
fi

if [ ! -r "$DOCKERFILE" ]
then
	echo "cannot find $DOCKERFILE (in $(readlink -e .)), abort"
	exit 1
fi

DOCKERFILE_DIR=$(dirname "$DOCKERFILE")
CONTAINER="${CONTAINER:-}"
[ -n "$CONTAINER" ] || CONTAINER=$(docker build -q -f "$DOCKERFILE" "$DOCKERFILE_DIR")

echo "running in container: $CONTAINER"

docker run \
  -t \
  $USER_FLAGS \
  -v $HOME:$HOME \
  -v $(pwd):$(pwd) \
  -w $(pwd) \
  "$CONTAINER" "$@"
