# CBMC Debian package

This builds the Debian package for CBMC, using an auto-generated changelog.

* Run `make` to
  * clone the latest release and build CBMC, and
  * create a Debian package `cbmc_<RELEASE>_<ARCHITECTURE>.deb` for that latest
    release.

Install with `sudo dpkg -i `cbmc_<RELEASE>_<ARCHITECTURE>.deb`.

Remove with `sudo dpkg -r cbmc`.
