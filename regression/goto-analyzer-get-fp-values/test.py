import sys
import os
import json
import subprocess

GotoAnalyzerPath = sys.argv[1]
TestCPath = sys.argv[2]
TestJsonPath = os.path.splitext(TestCPath)[0] + '.json'

subprocess.check_call([
  GotoAnalyzerPath,
  '--verify',
  TestCPath,
  '--variable-sensitivity',
  '--value-set',
  '--get-fp-values',
  TestJsonPath])

with open(TestJsonPath) as testJson:
  functionPointerValues = json.load(testJson)

def check(callsite_name, expectedValues):
  if set(functionPointerValues[callsite_name]) != set(expectedValues):
    print('Mismatch: {} expected to be {} but was {}'.format(
      callsite_name,
      expectedValues,
      functionPointerValues[callsite_name]))
    sys.exit(1)

check('fptr_is_g_or_h.function_pointer_call.1', ['g', 'h'])
check('fptr_is_bottom.function_pointer_call.1', [])
check('fptr_is_f.function_pointer_call.1', ['f'])

topFunctionPointerCallsite = 'fptr_is_top.function_pointer_call.1'
if topFunctionPointerCallsite in functionPointerValues:
  print('Not expecting `{}` to be present because it is TOP, but was {}'.format(
    topFunctionPointerCallsite,
    functionPointerValues[topFunctionPointerCallsite]))