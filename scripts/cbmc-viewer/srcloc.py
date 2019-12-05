"""Methods for maniuplating source locations found in cbmc output."""

import re
import os
import tempfile
from xml.etree import ElementTree

def warn(msg, abort=True):
    """Warn and possibly abort with an error message"""
    print(msg)
    if abort:
        raise UserWarning(msg)

def parse_xml_file(xml, abort=True):
    """Open and parse an xml file."""

    # Messages printed by cbmc before the coverage data we care about may
    # quote from the code, and quoted null character '\0' will appear as
    # the string '&#0', which is unparsable by ElementTree.

    try:
        with tempfile.NamedTemporaryFile(mode='w', delete=False) as outputf:
            with open(xml, 'r') as inputf:
                for line in inputf:
                    outputf.write(line.replace('&#0;', 'null_char'))
            outputf.seek(0)
            root = ElementTree.parse(outputf.name).getroot()
    except IOError as err:
        warn("Can't open xml file {}: {}".format(xml, err.strerror), abort)
        return None
    except ElementTree.ParseError as err:
        warn("Can't parse xml file {}: {}".format(xml, str(err)), abort)
        return None
    return root

def parse_xml_string(xml, abort=True, src=""):
    """Open and parse an xml string."""

    # Messages printed by cbmc before the coverage data we care about may
    # quote from the code, and quoted null character '\0' will appear as
    # the string '&#0', which is unparsable by ElementTree.

    try:
        root = ElementTree.fromstring(xml)
    except ElementTree.ParseError as err:
        warn("Can't parse xml string {}...{}: {}"
             .format(xml[:40],
                     " from {}".format(src) if src else "",
                     str(err)),
             abort)
        return None
    return root

def path_regexp(path):
    """Form a regular expression for several variants of a path"""

    path = path.rstrip(os.sep)+os.sep
    relpath = path if os.path.isabs(path) else "." + os.sep + path
    abspath = os.path.abspath(path) + os.sep
    realpath = os.path.realpath(path) + os.sep
    paths = [path, relpath, abspath, realpath]
    return "|".join(["({})".format(make_linux_path(path_)) for path_ in paths])

SOURCE_LOCATION_REGEXP = '(file ([^ ]*)) (function ?([^ ]*)) (line ([0-9]*))'
SOURCE_LOCATION_RE = re.compile(SOURCE_LOCATION_REGEXP)

def make_linux_path(path):
    """Turn a path (eg, a Windows path) into a Linux path."""
    return path.replace(os.sep, '/')

def make_linux_normpath(path):
    """Turn a path into a normalized Linux path."""
    return make_linux_path(os.path.normpath(path))

class SourceLocation:
    """Methods for maniuplating source locations found in cbmc output."""

    def __init__(self, root):
        """Create a source location object with a given root"""

        if root is None:
            self.root = None
            self.root_re = None
            self.path_from_root = {}
            return

        self.root = make_linux_normpath(root)
        self.root_re = re.compile(path_regexp(self.root))
        self.path_from_root = {}

    def strip_root(self, path):
        """Strip root from path name"""

        if path.startswith(self.root):
            return path[len(self.root):].lstrip('/')
        return path

    def scan_source_locations(self, xml):
        """Scan source locations appearing in xml produced by cbmc.
           Map each file to a path to the file relative to the source root."""

        for loc in xml.iter('location'):
            src_file = loc.get('file')
            src_dir = loc.get('working-directory')

            # Skip incomplete source locations
            if src_file is None or src_dir is None:
                continue

            # Skip built in functions
            if src_file.startswith('<builtin-'):
                self.path_from_root[src_file] = src_file
                continue

            # Compute file path relative to root
            # src_file may be an absolute path or relative to src_dir
            path = ('' if src_file.startswith('/') else src_dir + '/') + src_file
            path = make_linux_normpath(path)
            path = self.strip_root(path)

            # Map several variables of src_file to relative path
            src_file_linux = make_linux_path(src_file)
            src_file_normpath = make_linux_normpath(src_file)

            # Check for conflicts with prior source locations
            for old_path in [self.path_from_root.get(src_file),
                             self.path_from_root.get(src_file_linux),
                             self.path_from_root.get(src_file_normpath)]:
                if old_path is None or old_path == path:
                    continue
                print("Warning: file {} found in directories {} and {}"
                      .format(src_file, path, old_path))

            self.path_from_root[src_file] = path
            self.path_from_root[src_file_linux] = path
            self.path_from_root[src_file_normpath] = path

    def clean_path(self, path):
        """Strip root from a path"""

        path = make_linux_normpath(path)
        path = self.path_from_root.get(path) or path
        path = self.strip_root(path)
        return path

    def clean_source_location(self, line):
        """Strip root from a file name in a source location in a line"""

        match = SOURCE_LOCATION_RE.search(line)
        if match is None:
            return line

        prefix = line[:match.start(2)]
        path = match.group(2)
        suffix = line[match.end(2):]

        return prefix + self.clean_path(path) + suffix

################################################################
