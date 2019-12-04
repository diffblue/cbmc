"""Gather names of source files used to buid a goto binary."""

import os
import subprocess
import platform
import re

def find_sources(root, skip=None):
    """Find source files under root."""
    root = os.path.abspath(root)

    # Windows does not have a find command
    if platform.system() == 'Windows':
        files = find_sources_with_walk(root)
    else:
        files = find_sources_with_find(root)

    if skip:
        files = [name for name in files if not re.match(skip, name)]

    return files

def find_sources_with_find(root='.'):
    """Use find to list source files in subtree rooted at root."""
    cmd = ["find", "-L", ".",
           "(", "-iname", "*.[ch]", "-or", "-iname", "*.inl", ")"]
    try:
        find = subprocess.check_output(cmd, cwd=root).decode('utf-8')
    except:
        msg = "Can't annotate source files: "
        msg += "Can't run command '{}'".format(" ".join(cmd))
        print(msg)
        raise
    return find.strip().splitlines()

def find_sources_with_walk(root='.'):
    """Use walk to list source files in subtree rooted at root."""
    files = []
    for path, _, filenames in os.walk(root, followlinks=True):
        names = [os.path.join(path, name) for name in filenames
                 if name.lower().endswith((".h", ".c", ".inl"))]
        files.extend(names)
    dirlen = len(root) + 1
    files = [name[dirlen:].replace(os.sep, '/') for name in files]
    # find returns relative path names
    files = ['.' + os.sep + name for name in files]
    return files
