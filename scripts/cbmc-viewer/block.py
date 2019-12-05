"""Basic block coverage reporting for CBMC."""

import re
from pprint import pprint

import linestatus
import srcloc as SrcLoc

class Block:
    """Basic block coverage for CBMC.

    The Block class parses the basic block coverage information in the
    xml file produced by 'cbmc --cover locations --xml-ui' and
    provides three classes of coverage information:

        block.line[file][line] is the line status HIT, PARTIAL, MISS,
        or None giving whether this line in this file was hit or not.

        block.file[file] gives the line coverage for a file in the
        form of a tuple (coverage, hit, reachable) giving the number
        of reachable lines, the number of hit lines, and their ratio
        coverage.

        block.function[file][func] gives the line coverage for a
        function in a file in the form of a tuple (coverage, hit,
        reachable) giving the number of reachable lines, the number of
        hit lines, and their ratio coverage.
    """

    def __init__(self, xml="", srcdir="", blddir="",
                 reachable=None, srcloc=None):
        """Initialize block coverage statistics.

        Args:

           xml (str): the name of the xml file containing the block
           coverage data produced by cbmc.

           srcdir (str): the root of the source directory

           blddir (str): the root of the source directory used to
           build the goto binary (which may be different from srcdir
           if the source directory was preprocessed before building)

           reachable (obj): an instance of the Reachable class giving
           statistics on the statically reachable functions
        """

        # pylint: disable=too-many-arguments

        self.line = {}
        self.function = {}
        self.file = {}

        # Record the list of reachable functions for later use
        self.reachable = reachable.functions if reachable else []
        # Record the mapping of filenames computed below for later use
        # This should be using srcloc.clean_path
        self.cleanup_filename = Block.cleanup_filename_function(blddir or
                                                                srcdir)

        if not xml:
            return

        root = SrcLoc.parse_xml_file(xml, abort=False)
        if root is None:
            return
        srcloc.scan_source_locations(root)

        line_status = Block.line_status(root, srcloc)
        self.line = Block.line_coverage(line_status)
        self.function = Block.function_coverage(line_status)
        self.file = Block.file_coverage(line_status)

    @staticmethod
    def line_status(root, srcloc):
        """Compute reachability of a line in a source file."""

        # pylint: disable=too-many-locals

        line_status = {}

        for goal in root.iter("goal"):
            goal_description = goal.get("description")
            if not goal_description:
                break
            goal_status = goal.get("status")
            goal_loc = goal.find("location")
            loc_file = goal_loc.get("file")
            loc_func = goal_loc.get("function")
            loc_line = int(goal_loc.get("line"))

            lnst = (linestatus.HIT
                    if goal_status == "SATISFIED"
                    else linestatus.MISSED)

            locations = Block.parse_location_description(goal_description)
            if not locations:
                locations = [(loc_file, loc_func, loc_line)]

            for loc in locations:
                src, func, line = loc
                src = srcloc.clean_path(src)

                if not line_status.get(src):
                    line_status[src] = {}
                if not line_status[src].get(func):
                    line_status[src][func] = {}
                if not line_status[src][func].get(line):
                    line_status[src][func][line] = None
                line_status[src][func][line] \
                    = linestatus.combine(line_status[src][func][line],
                                         lnst)

        return line_status

    @staticmethod
    def line_coverage(line_status):
        """Coverage status of a line in a source file."""
        status = {}
        for src in line_status:
            if not status.get(src):
                status[src] = {}
            for func in line_status[src]:
                for line in line_status[src][func]:
                    status[src][line] = line_status[src][func][line]
        return status

    @staticmethod
    def file_coverage(line_status):
        """Fraction of reachable lines in a source file that were hit."""
        coverage = {}
        for src in line_status:
            reached = 0
            hit = 0
            for func in line_status[src]:
                for line in line_status[src][func]:
                    reached += 1
                    hit += 1 if line_status[src][func][line] else 0
            coverage[src] = (float(hit)/float(reached), hit, reached)
        return coverage

    @staticmethod
    def function_coverage(line_status):
        """Fraction of reachable lines in a source file that were hit."""
        coverage = {}
        for src in line_status:
            coverage[src] = {}
            for func in line_status[src]:
                coverage[src][func] = (0, 0, 0)
                reached = 0
                hit = 0
                for line in line_status[src][func]:
                    reached += 1
                    hit += 1 if line_status[src][func][line] else 0
                coverage[src][func] = (float(hit)/float(reached),
                                       hit, reached)
        return coverage

    def hit_functions(self):
        """Dynamically reachable functions.

        Return a list of tuples (file, function, coverage) for each
        function hit by CBMC.
        """
        functions = []
        for file_name in self.function:
            for func_name in self.function[file_name]:
                coverage = self.function[file_name][func_name]
                if coverage[0] > 0:
                    functions.append((self.cleanup_filename(file_name),
                                      func_name,
                                      coverage))
        return Block.sort_functions(functions)

    def reachable_functions(self):
        """Statically reachable functions.

        Returns a list of tuples (file, function, coverage) for each
        reachable function, or for hit functions if no reachable
        functions are recorded.
        """
        if not self.reachable:
            return self.hit_functions()

        functions = []
        for file_name in self.reachable:
            for func_name in self.reachable[file_name]:
                # cbmc records full pathnames for reachable functions
                file_name = self.cleanup_filename(file_name)
                try:
                    # Coverage for test harness probably missing
                    coverage = self.function[file_name][func_name]
                except KeyError:
                    continue
                functions.append((file_name, func_name, coverage))
        return Block.sort_functions(functions)

    @staticmethod
    def parse_location_block(blk):
        """Parse location block string 'file:func:lines,lines,lines'."""
        locations = []

        # Leftmost ":" may be part of Windows path name
        src, func, linestr = blk.rsplit(":", 2)
        if not src or not func or not linestr:
            return locations

        lines = re.split(',', linestr)
        if not lines:
            return locations

        for line_range in lines:
            if not line_range:
                continue
            # a line range can either be a single line or line1-line2
            bounds = line_range.split('-')
            if len(bounds) == 1:
                bounds.append(bounds[0])
            for line in range(int(bounds[0]), int(bounds[1]) + 1):
                locations.append((src, func, line))

        return locations

    @staticmethod
    def parse_location_blocks(blks):
        """Parse location blocks string 'block; block; block'."""
        locations = []

        blocks = re.split(';', blks)
        if not blocks:
            return locations

        for block in blocks:
            locations += Block.parse_location_block(block)

        return locations

    @staticmethod
    def parse_location_description(loc):
        """Parse location description '.... (lines blocks)'."""
        locations = []

        pattern = r".*\(\s*lines\s+(.*)\)"
        match = re.match(pattern, loc)
        if not match:
            return locations

        return Block.parse_location_blocks(match.group(1))

    @staticmethod
    def sort_functions(functions):
        """Sort a list of tuples (file, function, coverage)."""
        functions.sort(key=lambda tup: (tup[0], tup[1]))
        functions.sort(key=lambda tup: tup[2][0], reverse=True)
        return functions

    @staticmethod
    def cleanup_filename_function(path):
        """Clean up file names that begin with a path prefix."""
        if not path:
            return lambda n: n
        regexp = re.compile(SrcLoc.path_regexp(path))
        return lambda n: regexp.sub("", n)


if __name__ == "__main__":
    BLOCK = Block("results.xml")
    pprint(BLOCK.line)
