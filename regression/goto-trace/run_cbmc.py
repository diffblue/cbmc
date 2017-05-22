import json
import subprocess
import os
def run_cbmc(file, function, extra_args):
  cbmc_directory='../../../src/cbmc/'
  json_arg='--json-ui'
  args=[file, '--function', function, json_arg] + extra_args
  cbmc_process=subprocess.Popen([cbmc_directory + 'cbmc'] + args, stdout=subprocess.PIPE)
  output=cbmc_process.communicate()[0]
  print(output)
  return json.loads(output)
