"""Format report on loops in cbmc program."""
from __future__ import print_function

from builtins import object
import os
import sys
import subprocess

import srcloc as SrcLoc

class Loop(object):
    """The loops reported by cbmc with --show-loops."""

    def __init__(self, goto_pgm="", srcloc=None):
        """Initialize with xml output of 'cbmc --show-loops'.

        loop[name] is a dictionary mapping a loop name to a dictionary
        giving the file, function, and line number of the loop.

        index[file][function][line] is the name of the loop at the
        given location in the source code.
        """
        self.loop = {}
        self.index = {}

        if not goto_pgm:
            return
        try:
            cmd = ["cbmc", "--show-loops", "--xml-ui", goto_pgm]
            output = subprocess.check_output(cmd)
        except subprocess.CalledProcessError:
            print ("Can't find loops: "
                   'Unable to run command "{}"'.format(" ".join(cmd)))
            return

        root = SrcLoc.parse_xml_string(output)
        srcloc.scan_source_locations(root)

        for loop in root.iter("loop"):
            ident = loop.find("loop-id").text
            loc = loop.find("location")
            src = loc.get("file")
            func = loc.get("function")
            line = int(loc.get("line"))

            src = srcloc.clean_path(src)

            self.loop[ident] = {"file": src, "function": func, "line": line}

            if self.index.get(src, None) is None:
                self.index[src] = {}
            if self.index[src].get(func, None) is None:
                self.index[src][func] = {}
            self.index[src][func][line] = ident

    def markup_index(self):
        """Format loop index in the loop report."""
        html = []

        html.append('<ul>')
        for src in sorted(self.index):
            html.append('<li>{}'.format(src))
            html.append('<ul>')
            for func in sorted(self.index[src]):
                html.append('<li>{}'.format(func))
                html.append('<ul>')
                for line in sorted(self.index[src][func]):
                    html.append(('<li> <a href="{}.html#{}">{}</a> at '
                                 'line {}</li>')
                                .format(src, line,
                                        self.index[src][func][line], line))
                html.append('</ul>')
                html.append('</li>')
            html.append('</ul>')
            html.append('</li>')
        html.append('</ul>')

        return '\n'.join(html)

    def markup_id(self, ident):
        """Link loop identifier to the loop in the source code."""
        if self.loop.get(ident, None) is None:
            return None
        return ('<a href="{}.html#{}">{}</a>'
                .format(self.loop[ident]["file"], self.loop[ident]["line"],
                        ident))

    def markup_id_description(self, ident):
        """Format the loop identifier description in the loop report."""
        if self.loop.get(ident, None) is None:
            return None
        src = self.loop[ident]["file"]
        line = self.loop[ident]["line"]
        return ('<a href="{}.html#{}">{}</a> at line {} in file {}'
                .format(src, line, ident, line, src))

    def html_report(self, outfile):
        """Format the loop report."""
        path = os.path.dirname(outfile) or "."
        try:
            os.makedirs(path)
        except OSError:
            if not os.path.isdir(path):
                raise

        try:
            fp = open(outfile, "w")
        except IOError as e:
            print ("Unable to open {} for writing: {}"
                   .format(outfile, e.strerror))
            sys.exit()

        html = []
        html.append('<html><head><title>Loop index</title></head>'
                    '<body><h1>Loop index</h1>')
        html.append('<div style="font-family:courier">')
        html.append(self.markup_index())
        html.append('</div>')
        html.append('</body></html>')

        fp.write("\n".join(html))
        fp.close()
