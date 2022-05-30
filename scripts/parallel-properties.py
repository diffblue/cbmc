#!/usr/bin/env python3

"""Parallelise checking of all properties in a GOTO binary using CBMC

This script invokes a chosen number of parallel CBMC processes to check all the
properties contained in a given GOTO binary. Each of these processes will check
just a single property, possibly permitting slicing away considerable parts of
the program. The expected benefit is that the results for some of the
properties are reported very quickly, and that checking scales with the number
of available processing cores. On the downside, however, multiple invocations
of CBMC come with overhead, such as repeated symbolic execution.

Before running this script, the following must be true:

    1. "cbmc" must be in your system PATH
    2. A GOTO binary has been built from source (using goto-cc)
    3. The GOTO binary has been instrumented with all the required checks
       (using goto-instrument)

A typical usage of this script will be:

    scripts/parallel-properties.py -J 32 binary.gb --timeout 600

See --help for the list of available command-line options.
"""

import argparse
import colorama
from colorama import Fore, Style
import concurrent.futures
import json
import logging
import multiprocessing
import re
import subprocess
import sys
import threading
import time


def get_logger(verbose):
    # workaround for https://github.com/joblib/joblib/issues/692
    LOGGER_NAME = 'parallel-cbmc'
    logger = logging.getLogger(LOGGER_NAME)
    logging.basicConfig()
    if verbose:
        logger.setLevel('DEBUG')
    else:
        logger.setLevel('INFO')
    return logger


def add_to_stats(stats, key, value):
    key_path = key.split('/')
    k = key_path[0]

    if len(key_path) > 1:
        if not stats.get(k):
            stats[k] = {}
        add_to_stats(stats[k], '/'.join(key_path[1:]), value)
    else:
        if not stats.get(k):
            stats[k] = 0
        stats[k] += value


def merge_stats_rec(src, prefix, dest):
    if isinstance(src, dict):
        for k in src:
            p = prefix + '/' + k
            merge_stats_rec(src[k], p, dest)
    else:
        add_to_stats(dest, prefix[1:], src)


def merge_stats(src, dest):
    merge_stats_rec(src, '', dest)


def print_stats(stats):
    for cat in sorted(stats):
        print(cat + ':')
        csv = dict(stats[cat])
        columns = set()
        for s in csv:
            if isinstance(csv[s], dict):
                columns |= set(csv[s].keys())
        if not columns:
            print(cat + ',count')
            for s in sorted(csv):
                print('{},{}'.format(s, csv[s]))
        else:
            print(cat + ',' + ','.join(sorted(columns)))
            for s in sorted(csv):
                values = [s]
                for c in sorted(columns):
                    values.append(str(csv[s].get(c, 0)))
                print(','.join(values))


def run_cmd_checked(cmd, verbose):
    """
    Execute `cmd` in a subprocess and check the return code. Raise an exception
    if the return code is not 0.
    """
    proc = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True)
    (out, err) = proc.communicate()
    logger = get_logger(verbose)
    if logger.getEffectiveLevel() <= logging.DEBUG:
        with lock:
            logger.debug("BEGIN " + str(cmd))
            logger.debug(out)
            logger.debug(err)
            logger.debug("END " + str(cmd))
    if proc.returncode != 0:
        e = subprocess.CalledProcessError(proc.return_code, cmd, output=out)
        e.stdout = out
        e.stderr = err
        raise e
    return None


def run_cmd_with_timeout(cmd, timeout_sec, verbose):
    # http://www.ostricher.com/2015/01/python-subprocess-with-timeout/
    """
    Execute `cmd` in a subprocess and enforce timeout `timeout_sec` seconds.
    Return subprocess exit code on natural completion of the subprocess.
    Raise an exception if timeout expires before subprocess completes.
    """
    t1 = time.time()
    proc = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True)
    timer = threading.Timer(timeout_sec, proc.kill)
    out = None
    err = None
    try:
        timer.start()
        (out, err) = proc.communicate()
    finally:
        timer.cancel()
    t2 = time.time()
    cnf_vars = cnf_clauses = None
    m = re.search(r'(\d+) variables, (\d+) clauses', out)
    if m:
        cnf_vars = m[1]
        cnf_clauses = m[2]
    logger = get_logger(verbose)
    if logger.getEffectiveLevel() <= logging.DEBUG:
        with lock:
            logger.debug("BEGIN " + str(cmd))
            logger.debug(out)
            logger.debug("END " + str(cmd))
    return (proc.returncode, err, t2 - t1, cnf_vars, cnf_clauses)


C_ERROR = 'ERROR'
C_TIMEOUT = 'TIMEOUT'
C_TRUE = 'SUCCESS'
C_FALSE = 'FAILURE'


def source_location_as_string(loc):
    result = ''
    if loc.get('file'):
        result = 'file ' + loc['file']
    if loc.get('function'):
        result += ' function ' + loc['function']
    if loc.get('line'):
        result += ' line ' + loc['line']
    return result.lstrip()


def output_result(result_entry, stats, status, verbose):
    prop = result_entry['property']
    loc = "{}:{}".format("missing file", "missing line")

    result = {
            'property': prop,
            'sourceLocation': loc,
            'status': status,
            'time': result_entry['time']
            }

    """
    add_to_stats(stats, 'warning type/{}/total'.format(prop), 1)
    add_to_stats(stats, 'warning type/{}/{}'.format(prop, status.lower()), 1)
    add_to_stats(stats, 'total time'.format(analysis), result_entry['time'])
    """

    logger = get_logger(verbose)
    logger.debug('p:{}, r:{}'.format(prop['name'], status))
    if status == C_TRUE:
        c_status = Fore.GREEN + status + Style.RESET_ALL
    elif status == C_FALSE:
        c_status = Fore.RED + status + Style.RESET_ALL
    elif status == C_ERROR:
        c_status = Fore.YELLOW + status + Style.RESET_ALL
    else:
        c_status = Fore.BLUE + status + Style.RESET_ALL
    result_str = '[{}] {}: {}: {}'.format(
        prop['name'], source_location_as_string(prop['sourceLocation']),
        prop['description'], c_status)
    if result_entry['variables']:
        result_str += ' [{}/{}]'.format(result_entry['variables'],
                                        result_entry['clauses'])
    if status == C_ERROR:
        result_str += ' stderr: ' + result_entry['stderr']
    with lock:
        print(result_str)
    return (result, result_str)


def verify_one(goto_binary, unwind, unwindset, unwinding_assertions, depth,
               object_bits, prop, verbose, timeout, stats):
    # run CBMC with extended statistics
    cbmc_cmd = ['cbmc', '--verbosity', '8', goto_binary,
                '--property', prop['name'], '--reachability-slice',
                # '--full-slice',
                '--slice-formula']
    if unwind:
        cbmc_cmd.extend(['--unwind', unwind])
    if unwindset:
        cbmc_cmd.extend(['--unwindset', unwindset])
    if unwinding_assertions:
        cbmc_cmd.extend(['--unwinding-assertions'])
    if depth:
        cbmc_cmd.extend(['--depth', str(depth)])
    if object_bits:
        cbmc_cmd.extend(['--object-bits', str(object_bits)])
    (cbmc_ret, stderr_output, t, cnf_vars, cnf_clauses) = run_cmd_with_timeout(
            cbmc_cmd, timeout, verbose)
    result_entry = {'time': t, 'property': prop, 'variables': cnf_vars,
                    'clauses': cnf_clauses, 'stderr': stderr_output}
    if cbmc_ret == 0:
        return output_result(result_entry, stats, C_TRUE, verbose)
    elif cbmc_ret == 10:
        return output_result(result_entry, stats, C_FALSE, verbose)
    elif cbmc_ret < 0:
        return output_result(result_entry, stats, C_TIMEOUT, verbose)
    else:
        return output_result(result_entry, stats, C_ERROR, verbose)


def verify(goto_binary, unwind, unwindset, unwinding_assertions, depth,
           object_bits, verbose, timeout, n_jobs, stats):
    # find names of desired properties
    show_prop_cmd = ['goto-instrument', '--verbosity', '4', '--json-ui',
                     '--show-properties', goto_binary]
    props = subprocess.check_output(show_prop_cmd, universal_newlines=True)
    json_props = json.loads(props)
    if not json_props[1].get('properties'):
        return {}

    results = {}
    global lock
    lock = multiprocessing.Lock()

    with concurrent.futures.ThreadPoolExecutor(max_workers=n_jobs) as e:
        future_to_result = {e.submit(verify_one, goto_binary, unwind,
                                     unwindset, unwinding_assertions, depth,
                                     object_bits, prop, verbose, timeout,
                                     stats): prop
                            for prop in json_props[1]['properties']}
        for future in concurrent.futures.as_completed(future_to_result):
            prop = future_to_result[future]
            (result_json, result_str) = future.result()
            results[prop['name']] = result_json

    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
            '-j', '--json',
            type=str,
            help='write results to chosen file with JSON formatting'),
    parser.add_argument(
            '-s', '--statistics',
            action='store_true',
            help='output overall statistics')
    parser.add_argument(
            '-t', '--timeout',
            type=int, default=10,
            help='timeout (seconds) per analysis-tool invocation ' +
                 '(default: 10 seconds; use more time in case of timeouts)')
    parser.add_argument(
            '-J', '--parallel',
            type=int, default=11,
            help='run a specified number of a analyses in parallel')
    parser.add_argument(
            '-v', '--verbose',
            action='store_true',
            help='enable verbose output')
    parser.add_argument(
            '--unwind',
            type=str,
            help='loop unwinding, forwarded to CBMC'),
    parser.add_argument(
            '--unwindset',
            type=str,
            help='loop unwinding, forwarded to CBMC'),
    parser.add_argument(
            '--unwinding-assertions',
            action='store_true',
            help='enable unwinding assertions, forwarded to CBMC'),
    parser.add_argument(
            '--depth',
            type=int,
            help='symex depth, forwarded to CBMC'),
    parser.add_argument(
            '--object-bits',
            type=int,
            help='object bits, forwarded to CBMC'),
    parser.add_argument(
            'goto_binary',
            help='instrumented goto binary to verify')
    args = parser.parse_args()

    logger = get_logger(args.verbose)

    stats = {}
    results = {}
    results['results'] = verify(
            args.goto_binary, args.unwind, args.unwindset,
            args.unwinding_assertions,
            args.depth, args.object_bits, args.verbose,
            args.timeout, args.parallel, stats)

    if args.statistics:
        results['statistics'] = stats
        print_stats(stats)

    if args.json is not None:
        with open(args.json, 'w') as output_file:
            json.dump(results, output_file)


if __name__ == "__main__":
    colorama.init()
    rc = main()
    sys.exit(rc)
