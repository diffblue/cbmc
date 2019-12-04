"""Mark up the source tree and links into the source tree."""

import sys
import html
import os
import re
import errno

import linestatus
import sources

class Markup:
    """Mark up the source tree and links into the source tree."""

    def __init__(self, tags, coverage,
                 srcdir=".", htmldir="html", srcfilter=""):
        """Initialize marking up the source tree."""
        # pylint: disable=too-many-arguments
        self.tags = tags
        self.coverage = coverage
        self.srcdir = srcdir.rstrip('/')
        self.htmldir = htmldir.rstrip('/')
        self.srcfilter = srcfilter

    @staticmethod
    def src_html(src):
        """Map a source file path to the corresponding html file path."""
        return src+".html"

    def link_to_line(self, text, src, line, depth=0,
                     color=None, target=None):
        """Link text to a line in a source file."""
        # pylint: disable=too-many-arguments
        color = None if color == 'black' else color
        color = None if not color else color
        style = ' style="color:{}"'.format(color) if color else ''
        path = directory_ancestor(depth) + '/' + self.src_html(src)
        line = '#{}'.format(line) if line else ''
        tgt = ' target="{}"'.format(target) if target else ''
        return '<a{} href="{}{}"{}>{}</a>'.format(style, path, line, tgt, text)

    def link_to_file(self, text, src, depth=0, color=None, target=None):
        """Link text to a source file."""
        # pylint: disable=too-many-arguments
        return self.link_to_line(text, src, 0, depth, color, target)

    def link_symbol(self, symbol, depth=0, color=None, target=None, text=None):
        """Link a symbol to its definition."""
        # pylint: disable=too-many-arguments
        val = self.tags.lookup(symbol)
        if not val:
            return symbol

        text = text or symbol
        (src, line) = val[0]
        return self.link_to_line(text, src, line, depth, color, target)

    def link_file(self, src, depth=0, color=None):
        """Link a source file to its html file."""
        return self.link_to_file(src, src, depth, color)

    def link_function(self, function, depth=0, color=None):
        """Link a function to its definition."""
        return self.link_symbol(function, depth, color)

    def markup_source_location(self, loc, depth=0, color=None, target=None):
        # pylint: disable=too-many-locals
        """Link trace source location to file, line, and function."""

        match = re.search('(file ([^ ]+)) (function ([^ ]+)) (line ([^ ]+))', loc,
                          re.IGNORECASE)

        if not match:
            return loc

        file_text = match.group(1)
        file_text_start = match.start(1)
        file_text_end = match.end(1)
        file_name = match.group(2)
        file_link = self.link_to_file(file_text, file_name,
                                      depth, color, target)

        func_text = match.group(3)
        func_text_start = match.start(3)
        func_text_end = match.end(3)
        func_name = match.group(4)
        func_link = self.link_symbol(func_name, depth, color, target, func_text)

        line_text = match.group(5)
        line_text_start = match.start(5)
        line_text_end = match.end(5)
        line_num = match.group(6)
        line_link = self.link_to_line(line_text, file_name, line_num,
                                      depth, color, target)

        if file_name[0] == '<' and file_name[-1] == '>':
            return html.escape(loc, quote=False)

        return (loc[:file_text_start] + file_link +
                loc[file_text_end:func_text_start] + func_link +
                loc[func_text_end:line_text_start] + line_link +
                loc[line_text_end:])

    def markup_line(self, line, depth=0, color=None):
        """Mark up a source line with links to symbol definitions."""
        line = line.rstrip()
        line = untabify(line)
        line = html.escape(line, quote=False)
        tokens = re.split('([_a-zA-Z][_a-zA-Z0-9]*)', line)
        links = [self.link_symbol(tkn, depth, color) for tkn in tokens]
        newline = "".join(links)
        return newline

    def markup_file(self, indir, infile, outfile, depth, coverage):
        """Mark up a source file with links to symbol definitions."""
        # pylint: disable=too-many-arguments
        try:
            # Some files on Windows appear to use an encoding
            # incompatible with the Python 3 default utf-8.  Python 2
            # used to assume latin-1.  The utf-8 and latin-1 encodings
            # agree on ascii.
            infh = open(infile, "r", encoding="latin-1")
        except IOError as e:
            print("Unable to open {} for reading: {}".format(infile,
                                                             e.strerror))
            sys.exit()
        try:
            os.makedirs(os.path.dirname(outfile))
        except OSError as e:
            if e.errno != errno.EEXIST:
                raise
        try:
            outfh = open(outfile, "w", encoding="latin-1")
        except IOError as e:
            print("Unable to open {} for writing: {}".format(outfile,
                                                             e.strerror))
            sys.exit()

        # Strip source directory from source filename for the html page title
        filename = infile
        if filename.startswith(indir):
            filename = filename[len(indir):]
            filename = filename.lstrip('/')

        html_header(outfh, filename)
        lineno = 0
        for line in infh:
            lineno += 1
            ls = coverage.get(lineno) if coverage else None
            if ls is None:
                color = None
            elif ls == linestatus.HIT:
                color = "green"
            elif ls == linestatus.MISSED:
                color = "red"
            elif ls == linestatus.PARTIAL:
                color = "orange"
            line = self.markup_line(line, depth, color)
            try:
                html_line(outfh, line, lineno, color)
            except UnicodeEncodeError:
                print("UnicodeEncodeError:")
                print("file: {}".format(infile))
                print("line number: {}".format(lineno))
                print("line:")
                print(line)
                print("Skipping this line and continuing...")
        html_footer(outfh)

        infh.close()
        outfh.close()

    def markup_directory(self):
        """Mark up a source directory with links to symbol definitions."""
        try:
            os.makedirs(self.htmldir)
        except OSError as e:
            if not os.path.isdir(self.htmldir):
                print("Can't make directory {}: {}".format(self.htmldir,
                                                           e.strerror))
                sys.exit()
            if e.errno != errno.EEXIST:
                raise

        for src in source_files(self.srcdir, self.srcfilter):
            if src == '':
                continue
            if src[0] == '/':
                continue
            self.markup_file(self.srcdir,
                             self.srcdir+'/'+src,
                             self.htmldir+'/'+self.src_html(src),
                             directory_depth(src),
                             self.coverage.line.get(src))

################################################################


def untabify(string, tabstop=8):
    """Replace tabs with spaces in a line of code."""
    parts = re.split('(\t)', string)
    result = ''
    for s in parts:
        if s == '\t':
            result += ' '*(tabstop - (len(result) % tabstop))
            continue
        result += s
    return result

################################################################


def directory_depth(path):
    """Compute number of directories appearing in a path.

    The depth of dir1/dir2/dir3/file.c is 3.
    """
    path = path.strip().rstrip('/')
    return len(path.split('/'))-1


def directory_ancestor(depth):
    # pylint: disable=unused-variable
    """Compute path to the ancestor the given number of levels up.

    The directory redirection of depth 3 is ../../..
    """
    if depth < 1:
        return '.'
    return '/'.join(['..' for n in range(depth)])

################################################################


def source_files(srcdir, srcfilter=""):
    """Source files appearing in a source directory.

    Args:
        srcdir (str): the root of the source directory.
        srcfilter (str): a python regular expression for files to ignore.
    """
    cwd = os.getcwd()

    files = []

    try:
        os.chdir(srcdir)
    except OSError as e:
        msg = "Can't annotate source files: "
        msg += "Can't change to directory {}: {}".format(srcdir, e.strerror)
        print(msg)
        return []

    files = sources.find_sources(srcdir, srcfilter)
    files = [re.sub('^./', '', f) for f in files]

    try:
        os.chdir(cwd)
    except OSError as e:
        msg = "Can't annotate source files: "
        msg += "Can't change to directory {}: {}".format(cwd, e.strerror)
        print(msg)
        sys.exit()  # don't just return

    return files

################################################################


def html_header(fp, title):
    """Write the html header to a file."""
    fp.write("<html>\n")
    fp.write("<head><title>"+title+"</title></head>\n")
    fp.write("<body><pre>\n")


def html_footer(fp):
    """Write the html footer to a file."""
    fp.write("</pre></body>\n</html>\n")


def html_line(fp, line, lineno, color=None):
    """Write the annotated source line to an html file.

    Args:
        filep (str): a file handle open for writing
        line (str): the line of the source code
        lineno (int): the line number of the source code
        depth (int): the depth of the source code file below the source root
        tags (obj): the Tags object for the source tree
        color (str): the desired color for the source line
    """
    color = None if not color else color
    color = None if color == 'black' else color
    style = ' style="color:{}"'.format(color) if color else ''
    fp.write('<span id="{lineno}"{style}>{lineno:5} {line}</span>\n'.
             format(lineno=lineno, style=style, line=line))

################################################################
