# CBMC packages

This project builds installation packages for the tip of the develop
branch for MacOS, Windows, and Ubuntu.

There exist installation packages for the latest stable releases of
CBMC on MacOS and Ubuntu.

On MacOS:
* brew install cbmc

On Ubuntu:
* sudo apt-get install software-properties-common
* sudo add-apt-repository ppa:mt-debian/cbmc-backports
* sudo apt-get update
* sudo apt-get install cbmc

This project uses GitHub Actions to build installation packages for
the tip of the develop branch for MacOS, Windows, and Ubuntu each time
new commits is added to develop.  The packages reside on GitHub as
artifacts that can be listed using the GitHub Actions API.

A separate project implements a web page hosted on GitHub Pages that makes
it easy to find the installation package for the tip of develop.

The stable installation packages describe above for MacOS and Ubuntu
install into the local operating system's equivalent of
/usr/local/bin.
This project builds two kinds of packages:
* cbmc installs into the equvalent of /usr/local/bin
* cbmc-latest installs into the equivalent of /usr/local/cbmc-latest/bin,
  and makes it possible to have two copies of cbmc --- a stable release
  and a tip of develop --- side-by-side on the same machine.

For each operatin system:
* The MacOS package is just a tar file of a directory containing the
  binaries. The directory should be unpacked and placed in the search
  path. Using Homebrew, "brew install cbmc" will install the latest
  stable release.  These tar files are intended only to distribute the
  development versions between stable releases (Homebrew repository
  updates of the stable versions are quick).

* The Windows package is an Microsoft Installer (msi) for Windows 10
  with Visual Studio 2019.  It can be installed by double-clicking on the
  installer or runnin `msexec /i <filename>`.

* The Ubuntu package is a Debian package that can be installed with
  `dpkg -i <filename>`. There are packages for Ubuntu 18 and Ubuntu 16.
  These packages are intended to distribute the development versions
  between stable releases, but also to produce the stable packages uploaded
  to a Debian or Ubuntu PPA.

The file packages.yaml defines the workflow for GitHub Actions to build the
packages. Each package is defined by a job that runs in its own
container. The subdirectories contain files and data needed to build
each of the packages.
