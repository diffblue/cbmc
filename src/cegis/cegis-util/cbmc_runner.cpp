#include <cbmc/cbmc_parse_options.h>
#include <cbmc/bmc.h>
#include <goto-programs/goto_trace.h>
#include <cegis/cegis-util/temporary_output_block.h>

#define MOCK_ARGC 1u

namespace
{
const char * ARGV[]={ "cbmc" };

class cbmc_runnert: public cbmc_parse_optionst
{
  const symbol_tablet &st;
  const goto_functionst &gf;
  goto_tracet &trace;
  safety_checkert::resultt bmc_result;
public:
  cbmc_runnert(const symbol_tablet &st, const goto_functionst &gf,
      goto_tracet &trace) :
      cbmc_parse_optionst(MOCK_ARGC, ARGV), st(st), gf(gf), trace(trace), bmc_result(
          safety_checkert::UNSAFE)
  {
  }

  virtual ~cbmc_runnert()=default;

  virtual int get_goto_program(const optionst &options, bmct &bmc,
      goto_functionst &goto_functions)
  {
    symbol_table.clear();
    symbol_table=st;
    goto_functions.clear();
    goto_functions.copy_from(gf);
    if (process_goto_program(options, goto_functions)) return 6;
    return -1;
  }

  int do_bmc(bmct &bmc, const goto_functionst &goto_functions)
  {
    bmc.set_ui(get_ui());
    bmc_result=bmc.run(gf);
    trace=bmc.safety_checkert::error_trace;
    return 0;
  }

  safety_checkert::resultt get_bmc_result() const
  {
    return bmc_result;
  }

  const goto_tracet &get_trace() const
  {
    return trace;
  }
};
}

safety_checkert::resultt run_cbmc(const symbol_tablet &st,
    const goto_functionst &gf, goto_tracet &trace)
{
  const temporary_output_blockt disable_output;
  cbmc_runnert runner(st, gf, trace);
  const int result=runner.main();
  disable_output.release();
  if (EXIT_SUCCESS != result)
    throw std::runtime_error("cbmc_runner.cbmc-execution-failed");
  trace=runner.get_trace();
  return runner.get_bmc_result();
}
