"""Report the results of cbmc.

Report the results of cbmc with annotated source files indiciating
line coverage, with coverage reports for statically reachable functions,
and with lists of property violations and traces for each violation.
"""

import json
import os
import argparse

from trace import Trace
from property import Property
from result import Result
from tags import Tags
from loop import Loop
from reachable import Reachable
import errors
from block import Block
from markup import Markup
from srcloc import SourceLocation

################################################################


def command_line_parser():
    """Create the command line parser."""
    parser = argparse.ArgumentParser(
        description='Annotate source files with coverage information'
    )
    parser.add_argument(
        '--srcdir',
        default='.',
        metavar='DIR',
        help='Root of the source tree (default: ".")'
    )
    parser.add_argument(
        '--htmldir',
        default='html',
        metavar='DIR',
        help='Root of the html tree (default: "html")'
    )
    parser.add_argument(
        '--blddir',
        metavar='DIR',
        help=(
            'Root of the source tree used to build the goto '
            'program for cbmc.  This may be different from the '
            'actual source tree if SRC is preprocessed for '
            'cbmc. Defaults to srcdir.'
        )
    )
    parser.add_argument(
        '--goto',
        metavar='GOTO',
        help=(
            'The goto program built for cbmc. This can also be the source '
            'file from which cbmc itself generates the gogo program '
            '(default: "")'
        )
    )
    parser.add_argument(
        '--result',
        metavar='file.log',
        help='File containing output of cbmc (default: "")'
    )
    parser.add_argument(
        '--coverage',
        metavar='file.xml',
        help=(
            'Deprecated: '
            'File containing xml "--symex-coverage-report" line coverage '
            'data (default: "")'
        )
    )
    parser.add_argument(
        '--block',
        metavar='file.xml',
        help=(
            'File containing xml "--cover locations" block coverage data '
            '(default: "")'
        )
    )
    parser.add_argument(
        '--property',
        metavar='file.xml',
        help=(
            'File containing xml property definitions from '
            '--show-properties (default: "")'
        )
    )
    parser.add_argument(
        '--srcexclude',
        metavar='REGEXP',
        help=(
            'A grep regular expression for the source files to exclude '
            'from source annotation. The regular expression should match '
            'paths as they are returned by the find command run in SRC '
            'directory. (default: "")'
        )
    )
    parser.add_argument(
        '--json-summary',
        metavar='summary.json',
        help='File to write summary of key metrics to (in JSON format)'
    )
    return parser

################################################################


HIT = "hit"
LINES = "lines"
FUNCTIONS = "functions"


def coverage_detail_section(functions, markup):
    """Detailed report for the coverage section of the report."""
    detail = []
    code = {HIT: 0, LINES: 0, FUNCTIONS: 0}
    code_touched = {HIT: 0, LINES: 0, FUNCTIONS: 0}

    detail.append('<p>Coverage detail:</p>')
    detail.append('<table style="margin:auto; font-family:courier">')
    detail.append(('<tr><th>Coverage</th><th>Function</th>'
                   '<th>File</th></tr>'))
    for tup in functions:
        (src, fnc, (cov, hit, lines)) = tup
        detail.append(('<tr><td>{:.2f} ({}/{})</td><td>{}</td>'
                       '<td>{}</td></tr>')
                      .format(cov, hit, lines,
                              markup.link_function(fnc),
                              markup.link_file(src)))
        code[HIT] += hit
        code[LINES] += lines
        code[FUNCTIONS] += 1
        if cov > 0:
            code_touched[HIT] += hit
            code_touched[LINES] += lines
            code_touched[FUNCTIONS] += 1

    detail.append("</table>")
    return (detail, code, code_touched)


def coverage_summary_section(code, code_touched):
    """Summary report for the coverage section of the report."""
    summary = []
    summary.append('<p>Coverage summary:<ul>')
    if code_touched[LINES]:
        summary.append(('<li>{:.2f} ({} lines out of {} '
                        'statically-reachable lines in {} '
                        'functions reached)')
                       .format(float(code_touched[HIT]) /
                               float(code_touched[LINES]),
                               code_touched[HIT],
                               code_touched[LINES],
                               code_touched[FUNCTIONS]))
    if code[LINES]:
        summary.append(('<li>{:.2f} ({} lines out of {} '
                        'statically-reachable lines in {} '
                        'statically-reachable functions)')
                       .format(float(code[HIT]) / float(code[LINES]),
                               code[HIT],
                               code[LINES],
                               code[FUNCTIONS]))
    summary.append('</ul></p>')
    return summary


def error_section(result, properties, loops, traces, markup):
    """Error section of the report."""

    report = errors.assemble_report(result, properties)
    html = errors.format_report(report, markup, loops, traces)
    return html


def cbmc_report(result, coverage, properties, markup,
                htmldir="", loops=None, traces=None, json_summary=None):
    """Full cbmc report."""

    # pylint: disable=too-many-arguments,too-many-locals

    if htmldir:
        htmldir = htmldir.rstrip('/')+'/'
        try:
            os.makedirs(htmldir)
        except OSError:
            if not os.path.isdir(htmldir):
                raise

    html = []
    html.append('<html><head><title>Coverage</title></head><body>')
    html.append('<h1 style="text-align:center">CBMC report</h1>')

    summary_data = {}

    functions = coverage.reachable_functions() or coverage.hit_functions()
    if functions:
        detail, code, code_touched = coverage_detail_section(functions,
                                                             markup)
        summary = coverage_summary_section(code, code_touched)
        html.append('<h2 style="text-align:center">Line coverage</h2>')
        html += summary + detail
        summary_data['coverage'] = {}
        summary_data['coverage']['statically-reachable'] = code
        summary_data['coverage']['reached'] = code_touched

    html.append('<h2 style="text-align:center">Errors</h2>')
    err = error_section(result, properties, loops, traces, markup)
    html.append(err)
    # to be extended: record the number of properties as a first statistic
    stats = {'properties': len(properties.property)}
    summary_data['CBMC-stats'] = stats

    html.append("</body></html>")

    index = open(htmldir+'index.html', 'w')
    index.write("\n".join(html))
    index.close()

    if json_summary:
        with open(json_summary, 'w') as f:
            json.dump(summary_data, f)

################################################################

def main():
    """Construct the cbmc report."""
    parser = command_line_parser()
    args = parser.parse_args()

    # blddir defaults to srcdir
    args.blddir = args.blddir or args.srcdir

    # SourceLocation cleans up paths to source files. Among other
    # things, it maps file names appearing in goto source locations
    # to paths relative to the build root.
    srcloc = SourceLocation(args.blddir)

    reachable = Reachable(args.goto, srcloc)
    loop = Loop(args.goto, srcloc)
    tags = Tags(args.srcdir, fltr=args.srcexclude)

    block = Block(args.block,
                  srcdir=args.srcdir,
                  blddir=args.blddir,
                  reachable=reachable,
                  srcloc=srcloc)

    markup = Markup(tags, block, args.srcdir, args.htmldir, args.srcexclude)

    properties = Property(args.property, srcloc)
    result = Result(args.result)
    trace = Trace(args.result, markup, srcloc)

    loop.html_report("{}/loop.html".format(args.htmldir))
    trace.generate_traces(htmldir=args.htmldir, properties=properties)

    cbmc_report(result=result,
                coverage=block,
                properties=properties,
                markup=markup,
                htmldir=args.htmldir,
                loops=loop,
                traces=trace,
                json_summary=args.json_summary)

    markup.markup_directory()


if __name__ == "__main__":
    main()
