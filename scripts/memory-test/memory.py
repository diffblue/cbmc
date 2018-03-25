#!/usr/bin/env python

from __future__ import print_function

import argparse
import difflib
import fractions
import itertools
import msparser
import os
# import pprint
import sys


def near_eq(x, y):
    fx = float(x)
    fy = float(y)
    return abs(fy - fx) <= 0.1 * abs(fx)


class snapshot:
    def __init__(self, s, is_peak):
        self.data = s
        self.value = s['mem_heap']
        self.is_peak = is_peak

    def __cmp__(self, other):
        if self.__eq__(other):
            return 0
        else:
            return -1 if(self.value < other.value) else 1

    def __eq__(self, other):
        if self.is_peak != other.is_peak:
            return False

        if not near_eq(self.value, other.value):
            return False

        if self.data.get('heap_tree') and other.data.get('heap_tree'):
            ds = self.data['heap_tree']['children'][0]
            do = other.data['heap_tree']['children'][0]
            if ds['details']['function'] != do['details']['function'] or (
                    not near_eq(ds['nbytes'], do['nbytes'])):
                return False

        return True
        # pprint.pprint(self.data['heap_tree'], depth=2)
        # pprint.pprint(other.data['heap_tree'], depth=2)

    def __radd__(self, other):
        s = other + str(self.value)
        if self.is_peak:
            s += ' *peak*'
        if self.data.get('heap_tree'):
            d = self.data['heap_tree']['children'][0]
            s += ' {}: {}'.format(d['details']['function'], d['nbytes'])
        return s

    def __hash__(self):
        """
        Make sure all values end up in the same hash bucket to enforce
        comparision via ==/__eq__ as overridden above.
        """
        return 0


# based on https://chezsoi.org/lucas/blog/colored-diff-output-with-python.html
try:
    from colorama import Fore, init
    init()
except ImportError:  # fallback so that the imported classes always exist
    class ColorFallback():
        # simulate a subset of Colorama's features (Colorama knows how to
        # support Windows, we just don't support colours there)
        if sys.stdout.isatty and os.name != 'nt':
            GREEN = '\033[32m'
            RED = '\033[31m'
            RESET = '\033[0m'
        else:
            GREEN = RED = RESET = ''
    Fore = ColorFallback()


def color_diff(diff):
    for line in diff:
        if line.startswith('+'):
            yield Fore.GREEN + line + Fore.RESET
        elif line.startswith('-'):
            yield Fore.RED + line + Fore.RESET
        else:
            yield line


def build_sequence(data, peak_index):
    seq = []
    for si in range(0, len(data['snapshots'])):
        seq.append(snapshot(data['snapshots'][si], si == peak_index))
    seq.append(snapshot({'mem_heap': 0}, False))
    return seq


# based on
# https://stackoverflow.com/questions/1011938/python-previous-and-next-values-inside-a-loop
def previous_and_next(some_iterable):
    prevs, items, nexts = itertools.tee(some_iterable, 3)
    prevs = itertools.chain([None], prevs)
    nexts = itertools.chain(itertools.islice(nexts, 1, None), [None])
    return itertools.izip(prevs, items, nexts)


def interpolate(seq, other_seq):
    ls = len(seq) - 1
    lo = len(other_seq) - 1

    lcm = (ls * lo) / fractions.gcd(ls, lo)
    sub_steps = lcm / ls

    interpolated_seq = [seq[0]]
    for prev, item, nxt in previous_and_next(seq):
        if prev:
            step = (item.value - prev.value) // ls
            if step < 0:
                step += 1
            for i in range(0, sub_steps):
                s = snapshot(item.data, item.is_peak)
                s.value = prev.value + step * (i + 1)
                interpolated_seq.append(s)

    return interpolated_seq


def filter_delete(ref_seq, data_seq, add_elements, prev, item, nxt,
                  new_reference_seq, new_data_seq):
    (tag, i1, i2, j1, j2) = item
    fwd_only = False
    for d in ref_seq[i1:i2]:
        if prev and not fwd_only and data_seq[prev[4] - 1] == d:
            # the value from the original sequence would be
            # new_data_seq.append(data_seq[prev[4] - 1])
            # but since snapshot.__eq__ isn't transitive this may
            # result in having to do even more edits
            if add_elements:
                new_data_seq.append(d)
        elif nxt and data_seq[nxt[3]] == d:
            fwd_only = True
            # the value from the original sequence would be
            # new_data_seq.append(data_seq[nxt[3]])
            # but since snapshot.__eq__ isn't transitive this may
            # result in having to do even more edits
            if add_elements:
                new_data_seq.append(d)
        elif prev and nxt and (
                (ref_seq[prev[2] - 1] <= ref_seq[nxt[1]] and
                 ref_seq[prev[2] - 1] <= d and d <= ref_seq[nxt[1]]) or
                (ref_seq[prev[2] - 1] > ref_seq[nxt[1]] and
                 ref_seq[prev[2] - 1] >= d and d >= ref_seq[nxt[1]])):
            # the value from the original sequence would be between
            # new_data_seq.append(data_seq[prev[4] - 1]) and
            # new_data_seq.append(data_seq[nxt[3]])
            # but since snapshot.__eq__ isn't transitive this may
            # result in having to do even more edits
            if add_elements:
                new_data_seq.append(d)
        elif not add_elements:
            new_reference_seq.append(d)


def filter_insert(ref_seq, data_seq, add_elements, prev, item, nxt,
                  new_reference_seq, new_data_seq):
    (tag, i1, i2, j1, j2) = item
    fwd_only = False
    for i in data_seq[j1:j2]:
        if prev and not fwd_only and ref_seq[prev[2] - 1] == i:
            pass
        elif nxt and ref_seq[nxt[1]] == i:
            fwd_only = True
        elif prev and nxt and (
                (data_seq[prev[4] - 1] <= data_seq[nxt[3]] and
                 data_seq[prev[4] - 1] <= i and
                 i <= data_seq[nxt[3]]) or
                (data_seq[prev[4] - 1] > data_seq[nxt[3]] and
                 data_seq[prev[4] - 1] >= i and
                 i >= data_seq[nxt[3]])):
            pass
        else:
            new_data_seq.append(i)


def filter_diff(ref_seq, data_seq, add_elements):
    new_reference_seq = []
    if add_elements:
        new_reference_seq = ref_seq

    new_data_seq = []

    s = difflib.SequenceMatcher(None, ref_seq, data_seq)
    for prev, item, nxt in previous_and_next(s.get_opcodes()):
        (tag, i1, i2, j1, j2) = item
        if tag == 'equal':
            if not add_elements:
                new_reference_seq.extend(ref_seq[i1:i2])
            new_data_seq.extend(data_seq[j1:j2])
        elif tag == 'replace':
            filter_delete(ref_seq, data_seq, add_elements, prev, item, nxt,
                          new_reference_seq, new_data_seq)
            filter_insert(ref_seq, data_seq, add_elements, prev, item, nxt,
                          new_reference_seq, new_data_seq)
        elif tag == 'delete':
            filter_delete(ref_seq, data_seq, add_elements, prev, item, nxt,
                          new_reference_seq, new_data_seq)
        elif tag == 'insert':
            filter_insert(ref_seq, data_seq, add_elements, prev, item, nxt,
                          new_reference_seq, new_data_seq)

    return (new_reference_seq, new_data_seq)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-r', '--reference', type=str, required=True,
                        help='Massif reference output')
    parser.add_argument('-P', '--peak-diff', action='store_true',
                        help='Exit code depends on peak memory diff only')
    parser.add_argument('-F', '--fuzzy', action='store_true',
                        help='Permit varying numbers of snapsots')
    parser.add_argument('-A', '--artificial', action='store_true',
                        help='Add artificial elements [implies --fuzzy]')
    parser.add_argument('-I', '--interpolate', action='store_true',
                        help='Interpolate additional values between snapshots')
    parser.add_argument('file', type=str,
                        help='Massif output to validate')

    args = parser.parse_args()

    return args


def main():
    args = parse_args()

    reference_data = ()
    with open(args.reference) as r:
        reference_data = msparser.parse(r)

    data = ()
    with open(args.file) as f:
        data = msparser.parse(f)

    r_peak_index = reference_data['peak_snapshot_index']
    r_peak = reference_data['snapshots'][r_peak_index]
    peak_index = data['peak_snapshot_index']
    peak = data['snapshots'][peak_index]

    print("snapshots: ref={} cur={}".format(
        len(reference_data['snapshots']), len(data['snapshots'])))
    print("peak idx : ref={} cur={}".format(r_peak_index, peak_index))
    print("peak [kB]: ref={0:.2f} cur={1:.2f}".format(
        r_peak['mem_heap'] / 1024.0, peak['mem_heap'] / 1024.0))

    """
    snaps = min(len(reference_data['snapshots']), len(data['snapshots']))
    for i in range(0, snaps):
        print("mem_heap [kB]: ref={0:.2f} cur={1:.2f}".format(
            reference_data['snapshots'][i]['mem_heap'] / 1024.0,
            data['snapshots'][i]['mem_heap'] / 1024.0))
        print(snapshot(reference_data['snapshots'][i], False) ==
              snapshot(data['snapshots'][i], False))
    """

    reference_seq = build_sequence(reference_data, r_peak_index)
    data_seq = build_sequence(data, peak_index)

    if args.interpolate:
        reference_seq = interpolate(reference_seq, data_seq)
        data_seq = interpolate(data_seq, reference_seq)

    if args.fuzzy or args.artificial:
        (new_ref_seq, new_data_seq) = filter_diff(
                reference_seq, data_seq, args.artificial)
    else:
        (new_ref_seq, new_data_seq) = (reference_seq, data_seq)

    ret_code = 0
    diff = color_diff(
            difflib.unified_diff(
                new_ref_seq, new_data_seq, 'ref', 'cur', n=1, lineterm=''))
    for l in diff:
        ret_code = 1
        print(l)

    if args.peak_diff:
        r_peak = snapshot(reference_data['snapshots'][r_peak_index], True)
        d_peak = snapshot(data['snapshots'][peak_index], True)
        ret_code = 0 if r_peak == d_peak else 1

    return ret_code


if __name__ == '__main__':
    rc = main()
    sys.exit(rc)
