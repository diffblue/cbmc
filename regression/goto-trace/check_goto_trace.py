import re
import json

def check_class_identifier_step(trace_step):
  if 'lhs' in trace_step:
    lhs_value=trace_step["lhs"]
    is_lhs_class_identifier=re.search('@class_identifier', lhs_value)
    is_assignment=trace_step["stepType"]=='assignment'

    if is_lhs_class_identifier and is_assignment:
      rhs_value=trace_step['value']
      return 'data' in rhs_value and rhs_value['data']!=''

  # This isn't a relevant trace step
  return True

def check_trace_step(trace_step):
  step_valid=True
  checks=[check_class_identifier_step]
  for step_check in checks:
    if not step_check(trace_step):
      print("Step check " + str(step_check) + "failed")
      print(trace_step)
      step_valid=False

  return step_valid


def check_trace(trace):
  trace_valid=True
  step_index=0
  for step in trace:
    if 'stepType' in step:
      step_result=check_trace_step(step)
      if not step_result:
        print('Step ' + step_index + ' invalid')
        trace_valid=False
    else:
      print("Trace contains invalid step: no stepType")
      print(step)
      trace_valid=False

  return trace_valid

def get_traces(test_generator_output):
  for entry in test_generator_output:
    if('tests' in entry):
      for test in entry['tests']:
        yield test['trace']