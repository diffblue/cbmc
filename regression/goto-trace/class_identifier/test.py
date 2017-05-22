#!/usr/bin/python

import sys
sys.path.insert(0, '../')

import run_cbmc
import check_goto_trace

file='TestGenTest.class'
function='TestGenTest.f'

json_output=run_cbmc.run_cbmc(file, function, ['--trace',  '--cover', 'location']) #
traces=check_goto_trace.get_traces(json_output)

trace_found=False

for trace in traces:
  trace_found=True
  if check_goto_trace.check_trace(trace):
    requirements = {
      'lhs': 'tmp_object_factory$2.@java.lang.Object.@class_identifier',
      'value': { 'data' : 'java::TestGenTest', 'name': 'string'},
      'stepType': 'assignment'
    }

    if check_goto_trace.check_step_existence(trace, requirements):
      print("Trace valid")
    else:
      print("Trace invalid")
  else:
    print("Trace invalid")

if not trace_found:
  print("No trace found")

