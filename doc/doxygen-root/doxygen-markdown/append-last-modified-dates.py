#!/usr/bin/env python3

import git
import logging
import subprocess
import sys
from pathlib import Path

def append_last_modified_date(repo, path):
    """Append last modified date to a file"""

    # Use the author date %ai as last modified date and not the commit date %ci
    # The author date is what 'git log' prints from the command line
    date = repo.git.log("-1", "--format=%ai", path)

    with open(path, "a") as handle:
        # append two newlines to guarantee a paragraph break in the
        # new markdown file in the event the file does not already end
        # with a newline
        print(f"\n\nLast modified: {date}", file=handle)

def append_last_modified_dates(paths):
    paths = [Path(path).resolve() for path in paths]
    if not paths:
        logging.info("Failed to append last modified dates: list of files is empty")
        sys.exit(1)

    repo = git.Repo(paths[0], search_parent_directories=True)
    if repo.is_dirty():
        logging.info("Failed to append last modified dates: repository has uncommitted changes")
        sys.exit(1)

    for path in paths:
        append_last_modified_date(repo, path)

def main():
    fmt = '%(levelname)s: %(message)s'
    logging.basicConfig(level=logging.INFO, format=fmt)
    append_last_modified_dates(sys.argv[1:])

if __name__ == "__main__":
    main()
