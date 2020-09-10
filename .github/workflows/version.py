#!/usr/bin/env python3

import sys

def debian_number(major='0', minor='0', patch='0', build='0'):
    """Generate a Debian package version number from components."""
    return "{}.{}.{}-{}".format(major, minor, patch, build)

def version_number(version, build="0"):
    """Generate a Debian package version number."""

    parts = version.split('.')
    if len(parts) > 3:
        raise UserWarning("Version number {} contains {} components, "
                          "expected at most 3".format(version, len(parts)))

    major, minor, patch = (parts + ["0", "0", "0"])[:3]
    return debian_number(major, minor, patch, build)

def main():
    version = sys.argv[1] if len(sys.argv) > 1 else "0"
    build = sys.argv[2] if len(sys.argv) > 2 else "0"
    print(version_number(version, build))

if __name__ == "__main__":
    main()
