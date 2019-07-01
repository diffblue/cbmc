"""Format report of property violations found by cbmc."""
from __future__ import print_function

import re

ERROR = 0
WARNING = 1
PROP = "MISSINGPROP"
LOOP = "MISSINGLOOP"


def assemble_report(result, properties):
    """Map property violations in result to source line of the violation."""
    report = {}
    report[PROP] = {}
    report[PROP][ERROR] = []
    report[PROP][WARNING] = []
    report[LOOP] = {}
    report[LOOP][ERROR] = []
    report[LOOP][WARNING] = []
    for name in result.failures():
        kind = ERROR if result.error.get(name) else WARNING
        prop = properties.lookup(name)
        if not prop:
            print("Warning: Can't find property {}".format(name))
            if re.match(r'.*\.unwind\.[0-9]+$', name):
                report[LOOP][kind].append(name)
            else:
                report[PROP][kind].append(name)
            continue
        func = prop["function"]
        src = prop["file"]
        line = int(prop["line"])
        desc = prop["description"]

        if not report.get(src):
            report[src] = {}
        if not report[src].get(func):
            report[src][func] = {}
        if not report[src][func].get(line):
            report[src][func][line] = {}
        if not report[src][func][line].get(ERROR):
            report[src][func][line][ERROR] = []
        if not report[src][func][line].get(WARNING):
            report[src][func][line][WARNING] = []
        report[src][func][line][kind].append((name, desc))
    report[PROP][ERROR].sort()
    report[PROP][WARNING].sort()
    report[LOOP][ERROR].sort()
    report[LOOP][WARNING].sort()
    return report


def format_report(report, markup, loops=None, traces=None):
    """Format report on property violations."""

    # pylint: disable=too-many-branches

    html = ['<div style="font-family:courier">']

    if report[LOOP][ERROR] or report[LOOP][WARNING]:
        html.append('<ul>')
        html.append('<li>Loop unwinding failures '
                    '(<a href="loop.html">loop index</a>)')
        html.append('<ul>')
        for name in report[LOOP][ERROR]:
            html.append('<li>[{}] Loop {}</li>'
                        .format(traces.link_trace(name, "trace"),
                                markup_unwinding_error(name, loops)))
        for name in report[LOOP][WARNING]:
            html.append('<li>Warning [{}] Loop {}</li>'
                        .format(traces.link_trace(name, "trace"),
                                markup_unwinding_error(name, loops)))
        html.append('</ul>')
        html.append('</li>')
        html.append('</ul>')

    if report[PROP][ERROR] or report[PROP][WARNING]:
        html.append('<ul>')
        html.append('<li>Unknown property failures')
        html.append('<ul>')
        for name in report[PROP][ERROR]:
            html.append('<li>[{}] {}</li>'
                        .format(traces.link_trace(name, "trace"), name))
        for name in report[PROP][WARNING]:
            html.append('<li>Warning [{}] {}</li>'
                        .format(traces.link_trace(name, "trace"), name))
        html.append('</ul>')
        html.append('</li>')
        html.append('</ul>')

    html.append("<ul>")
    for src in sorted(report):
        if src == LOOP:
            continue
        if src == PROP:
            continue

        # built-in functions filenames given as "<filename>"
        match = re.match('^<(.*)>$', src)
        if match:
            html.append("<li>In {}<ul>".format(match.group(1)))
        else:
            html.append("<li>In {}<ul>".format(markup.link_file(src)))

        for func in sorted(report[src]):
            html.append("<li>In {}<ul>".format(markup.link_function(func)))
            for line in sorted(report[src][func]):
                html.append("<li>Line {}:<ul>"
                            .format(markup.link_to_line(line, src, line)))
                for error in sorted(report[src][func][line][ERROR]):
                    html.append("<li>[{}] {}</li>"
                                .format(traces.link_trace(error[0],
                                                          "trace"),
                                        error[1]))
                for error in sorted(report[src][func][line][WARNING]):
                    html.append("<li>Warning [{}] {}</li>"
                                .format(traces.link_trace(error[0],
                                                          "trace"),
                                        error[1]))
                html.append("</ul></li>")
            html.append("</ul></li>")
        html.append("</ul></li>")
    html.append("</ul>")

    html.append('</div>')
    return "\n".join(html)


def markup_unwinding_error(error, loops=None):
    """Format report on unwinding assertion violations."""
    if not loops:
        return error

    match = re.match(r'(.*)\.unwind\.(.*)', error)
    if not match:
        return error

    name = '{}.{}'.format(match.group(1), match.group(2))
    return loops.markup_id_description(name)
