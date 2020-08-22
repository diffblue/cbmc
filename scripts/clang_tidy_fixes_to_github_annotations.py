#!/usr/bin/env python3

# requires Python 3 >= 3.2
import argparse
import subprocess
import glob
import os
import sys
import bisect
import json
import tempfile

# PyYaml
import yaml

# local libraries
import diff_to_added_lines


class Diagnostic:
    def __init__(self, source_location, message, fix_suggestion=None):
        self.source_location = source_location
        self.message = message
        self.fix_suggestion = fix_suggestion


class SourceLocation:
    def __init__(self, line_number, column):
        self.line_number = line_number
        self.column = column


class OffsetToSourceLocation:
    def __init__(self, filename):
        self.line_offsets = []
        last_offset = 0
        with open(filename, 'rb') as file:
            for line in file:
                self.line_offsets.append(last_offset)
                last_offset = file.tell()

    def get_source_location_from_offset(self, offset):
        assert offset >= 0
        # bisect_right will return a number 1 greater than the index
        # of the smallest element in the list which is >= the searched value
        # Since line numbers start with 1 rather than 0 this exactly corresponds
        # to a line number, and we need to subtract one to get the index of the
        # corresponding offset of the file for the start of the line
        line_number = bisect.bisect_right(self.line_offsets, offset)

        # columns also start at 1 so we need to add 1
        column = offset - self.line_offsets[line_number - 1] + 1
        return SourceLocation(line_number, column)

    def get_file_offset_from_line_number(self, line_number):
        assert 0 < line_number <= len(self.line_offsets)
        return self.line_offsets[line_number - 1]


def build_fix_suggestion(source_file, offset_to_source_location, source_location, yaml_replacements):
    min_line = source_location.line_number
    max_line = source_location.line_number
    # we need this to be sorted further down the line
    yaml_replacements = sorted(yaml_replacements, key=(lambda replacement: replacement['Offset']))
    # this whole shebang is because we want to read whole lines
    replacement_locations = [offset_to_source_location.get_source_location_from_offset(replacement['Offset']) for
                             replacement in yaml_replacements]
    for replacement_location in replacement_locations:
        min_line = min(min_line, replacement_location.line_number)
        max_line = max(max_line, replacement_location.line_number)
    min_line_offset = offset_to_source_location.get_file_offset_from_line_number(min_line)
    max_line_offset = offset_to_source_location.get_file_offset_from_line_number(max_line)
    assert min_line_offset <= max_line_offset

    source_file.seek(min_line_offset)
    text_as_bytes = source_file.read(max_line_offset - min_line_offset)
    text_as_bytes += source_file.readline()  # read the last line in the range as well

    # because suggestion locations are byte based we go through the bytes here
    suggestions_applied = b''
    text_offset = 0
    for replacement in yaml_replacements:
        file_offset = replacement['Offset']
        offset_from_text_start = file_offset - min_line_offset
        suggestions_applied += text_as_bytes[text_offset:offset_from_text_start]
        # we get the replacement text as str so we need to encode it back to (utf-8) bytes
        suggested_replacement = replacement['ReplacementText'].encode()
        suggestions_applied += suggested_replacement
        text_offset = offset_from_text_start + replacement['Length']
    suggestions_applied += text_as_bytes[text_offset:]

    # convert to string before returning
    return suggestions_applied.decode()


def parse_diagnostic(source_file, offset_to_source_location, yaml_diagnostic):
    source_location = offset_to_source_location.get_source_location_from_offset(yaml_diagnostic['FileOffset'])
    message = yaml_diagnostic['Message']
    fix_suggestion = None
    if len(yaml_diagnostic['Replacements']) != 0:
        fix_suggestion = build_fix_suggestion(source_file, offset_to_source_location, source_location,
                                              yaml_diagnostic['Replacements'])
    return Diagnostic(source_location, message, fix_suggestion)


def parse_diagnostics(source_file_name, yaml_diagnostics):
    """turn clang-tidy diagnostics into our Diagnostic type"""
    diagnostics = []
    offset_to_source_location = OffsetToSourceLocation(source_file_name)
    with open(source_file_name, 'rb') as source_file:
        for yaml_diagnostic in yaml_diagnostics:
            # this can be violated with clang-analyzer, because clang-analyzer might
            # report an issue that is *reachable* from a source file but exists in a different file
            # (of course theoretically also possible that this might happen with other linting passes)
            # in any case, we can’t really report failures in other files (which might not even be in the diff)
            # in annotations (especially clang-analyzer tends to produce *very* long stack traces), so we ignore
            # these cases for now. Future work perhaps.
            if yaml_diagnostic['DiagnosticMessage']['FilePath'] == source_file_name:
                diagnostics.append(
                    parse_diagnostic(source_file, offset_to_source_location, yaml_diagnostic['DiagnosticMessage']))
    return diagnostics


def load_fixes(fixes_dir):
    """Get file fixes as a map from filename to a list of diagnostics"""
    fixes = {}
    for fixes_filename in glob.glob(os.path.join(fixes_dir, '*.yaml')):
        with open(fixes_filename) as fixes_file:
            file_fixes_yaml = yaml.load(fixes_file, Loader=yaml.Loader)
            source_file_name = file_fixes_yaml['MainSourceFile']
            diagnostics = parse_diagnostics(source_file_name, file_fixes_yaml['Diagnostics'])
            fixes[source_file_name] = diagnostics
    return fixes


def fixes_to_github_annotations(fixes, source_dir):
    annotations = []
    for filename in fixes:
        assert filename.startswith(source_dir + '/')
        relative_filename = filename[len(source_dir) + 1:]
        for fix in fixes[filename]:
            message = fix.message
            if fix.fix_suggestion:
                message += "\n```suggestion\n" + fix.fix_suggestion + "```"
            annotations.append({'message': message, 'path': relative_filename,
                                'start_column': fix.source_location.column, 'end_column': fix.source_location.column,
                                'start_line': fix.source_location.line_number, 'end_line': fix.source_location.line_number,
                                'annotation_level': 'warning'})
    return annotations


def remove_fixes_from_lines_that_are_not_in_diff(fixes, source_base_directory, git_base_ref, git_changes_ref):
    (patchfile, patchfile_name) = tempfile.mkstemp()
    git_diff_command = [b'git',
                        b'-C', source_base_directory.encode(),
                        b'diff',
                        git_base_ref.encode(),
                        git_changes_ref.encode()]

    git_result = subprocess.call(git_diff_command, stdout=patchfile)
    # if everything is set up correctly this should never fail
    assert git_result == 0
    added_lines = diff_to_added_lines.diff_to_added_lines(patchfile_name, source_base_directory)
    filtered_fixes = {}
    for fix_filename in fixes:
        filtered_fixes[fix_filename] = list(
            filter(lambda fix: fix.source_location.line_number in added_lines[fix_filename], fixes[fix_filename]))
    return filtered_fixes


def main():
    parser = argparse.ArgumentParser(description='Convert clang-tidy fixes in YAML format to github annotations JSON')
    parser.add_argument('--source-base-directory', metavar='DIR',
                        help='the base directory of the git repository',
                        required=True)
    parser.add_argument('--git-base-ref', metavar='SHA-branch-or-tag',
                        required=True,
                        help='the git ref we’re basing our changes on')
    parser.add_argument('--git-changes-ref', metavar='SHA-branch-or-tag',
                        help='the git ref that has our changes (default: HEAD)',
                        default='HEAD')
    parser.add_argument('--fixes-directory', metavar='DIR',
                        required=True,
                        help='the directory containing our fixes')

    options = parser.parse_args()
    fixes = load_fixes(options.fixes_directory)
    fixes = remove_fixes_from_lines_that_are_not_in_diff(fixes, options.source_base_directory,
                                                         options.git_base_ref, options.git_changes_ref)
    annotations = fixes_to_github_annotations(fixes, options.source_base_directory)
    json.dump(annotations, sys.stdout)
    # json.dump doesn’t print a newline
    print()


main()
