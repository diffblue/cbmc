#!/usr/bin/python

'''
This script collects the running times of the tests present in the current
directory.

It does not run the tests but reads the already present output files.

Usage:
    python performance.py

Dependencies:
    gnuplot http://www.gnuplot.info/
'''

import time
from subprocess import check_output
from subprocess import check_call

git_output = check_output(['git', 'show', 'HEAD'])
commit = git_output.split('\n')[0]
commit_id = time.strftime('%Y_%m_%d__%H_%M_%S')+'__'+commit[7:]

process = check_output(['grep', '^Runtime decision procedure', '-R'])
file_name = 'performance_'+commit_id+'.out'

print 'writing to file', file_name

with open(file_name, 'w') as f:
    f.write(process)

print('drawing to file', file_name+'.png')
check_call(['gnuplot', '-e', 'file="'+file_name+'"', '-e',
            'outputfile="'+file_name+'.png"', 'performance_draw.gp'])
