"""The error traces from CBMC."""

import os
import re
import sys


class Trace:
    """Parse, markup, and manage error traces."""

    def __init__(self, log, markup, srcloc):
        """Initialize error traces from cbmc output."""
        self.trace = {}
        self.markup = markup

        if not log:
            return

        try:
            fp = open(log, "r")
        except IOError as e:
            print(("Can't read cbmc traces: "
                   "Unable to open {} for reading: {}")
                  .format(log, e.strerror))
            return

        name = ""
        trace = ""
        for line in fp:
            match = re.match('^Trace for (.*):', line)
            if match:
                if name:
                    self.trace[name] = trace
                name = match.group(1)
                trace = ""
                continue
            if name:
                trace += srcloc.clean_source_location(line)
        if name:
            self.trace[name] = trace

        self.markup = markup


    def lookup(self, error):
        """Look up trace by error name."""
        return self.trace.get(error, None)

    def link_trace(self, error, text=""):
        """Link to a trace by error name."""
        text = text or error

        trace = self.lookup(error)
        if not trace:
            return text

        return '<a href="traces/{}.html">{}</a>'.format(error, text)

    def markup_trace(self, trace):
        """Annotate a trace."""
        lines = []
        for line in trace.split('\n'):
            lines.append(self.markup.markup_source_location(line,
                                                            depth=1,
                                                            target="code"))
        return "\n".join(lines)

    def generate_trace(self, error, htmldir="", htmlfile="", properties=None):
        """Generate an annotated trace file."""
        trace = self.lookup(error)
        if not trace:
            return

        filedir = htmldir or 'html'
        filedir = "{}/traces".format(filedir)
        filename = htmlfile or '{}.html'.format(error)
        filepath = '{}/{}'.format(filedir, filename)

        try:
            os.makedirs(filedir)
        except OSError:
            if not os.path.isdir(filedir):
                raise

        try:
            fp = open(filepath, "w")
        except IOError as e:
            print("Unable to open {} for writing: {}" \
                .format(filepath, e.strerror))
            sys.exit()

        html = []
        html.append('<html><head><title>{e}</title></head><body><h1>{e}</h1>'
                    .format(e=error))
        html.append('Trace for {}:'
                    .format(self.markup_error_description(error, properties)))
        html.append('<pre>')
        html.append(self.markup_trace(trace))
        html.append('</pre>')
        html.append('</body></html>')

        fp.write("\n".join(html))
        fp.close()

    def generate_traces(self, htmldir=None, htmlfile=None, properties=None):
        """Generate all annotated trace files."""
        for error in self.trace:
            self.generate_trace(error, htmldir=htmldir, htmlfile=htmlfile,
                                properties=properties)

    @staticmethod
    def markup_error(error, properties=None):
        """Link an error name to an annotated source code line."""
        if not (properties and properties.property.get(error, None)):
            return error
        srcfile = properties.property[error]["file"]
        line = properties.property[error]["line"]
        return '<a href="../{}.html#{}">{}</a>'.format(srcfile, line, error)

    @staticmethod
    def markup_error_description(error, properties=None):
        """Link an error description to an annotated source code line."""
        if not (properties and properties.property.get(error, None)):
            return error
        srcfile = properties.property[error]["file"]
        line = properties.property[error]["line"]
        return ('<a href="../{src}.html#{line}">{error}</a> '
                'at line {line} in file {src}'
                .format(src=srcfile, line=line, error=error))
