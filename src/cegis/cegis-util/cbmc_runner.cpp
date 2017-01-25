/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/config.h>
#include <util/substitute.h>

#include <cbmc/cbmc_parse_options.h>
#include <cbmc/bmc.h>

#include <goto-programs/goto_trace.h>
#include <goto-programs/write_goto_binary.h>

#include <cegis/options/parameters.h>
#include <cegis/cegis-util/temporary_output_block.h>
#include <cegis/cegis-util/cbmc_runner.h>

#define ARGV_MAX_SIZE 5u

namespace
{
bool exists(const std::string &name)
{
  return std::ifstream(name).good();
}

std::string get_goto_file_name(const size_t index)
{
  std::string name("cbmc_runner-");
  name+=std::to_string(index);
  return name+=".exe";
}

std::string get_next_goto_file_name()
{
  size_t index=0;
  while (exists(get_goto_file_name(index)))
    ++index;
  return get_goto_file_name(index);
}

bool is_gcc()
{
  return configt::ansi_ct::flavourt::GCC == config.ansi_c.mode;
}

int argc()
{
  return is_gcc()?3:2;
}

const char **argv()
{
  static const char* n_gcc[]={"cbmc", "--stop-on-fail", 0};
  static const char* w_gcc[]={"cbmc", "--stop-on-fail", "--gcc", 0};

  return is_gcc()?w_gcc:n_gcc;
}

class cbmc_runnert:public cbmc_parse_optionst
{
  const symbol_tablet &st;
  const goto_functionst &gf;
  cbmc_resultt &result;
  safety_checkert::resultt bmc_result;
  const bool keep_goto_programs;

public:
  cbmc_runnert(const symbol_tablet &st, const goto_functionst &gf,
      cbmc_resultt &result, const bool keep_goto_programs) :
      cbmc_parse_optionst(argc(), argv()), st(st), gf(gf), result(result), bmc_result(
          safety_checkert::UNSAFE), keep_goto_programs(keep_goto_programs)
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
    if (keep_goto_programs)
    {
      const std::string path(get_next_goto_file_name());
      message_handlert &msg=get_message_handler();
      write_goto_binary(path, symbol_table, goto_functions, msg);
    }

    return -1;
  }

  int do_bmc(bmct &bmc, const goto_functionst &goto_functions)
  {
    bmc.set_ui(get_ui());
    result.symbol_table.clear();
    result.symbol_table=symbol_table;
    result.goto_functions.clear();
    result.goto_functions.copy_from(goto_functions);
    bmc_result=bmc.run(result.goto_functions);
    result.trace=bmc.safety_checkert::error_trace;
    return 0;
  }

  safety_checkert::resultt get_bmc_result() const
  {
    return bmc_result;
  }
};
}

safety_checkert::resultt run_cbmc(const symbol_tablet &st,
    const goto_functionst &gf, cbmc_resultt &cbmc_result,
    const bool keep_goto_programs)
{
  const temporary_output_blockt disable_output;
  cbmc_runnert runner(st, gf, cbmc_result, keep_goto_programs);
  const int result=runner.main();
  disable_output.release();
  if (EXIT_SUCCESS != result)
    throw std::runtime_error("cbmc_runner.cbmc-execution-failed");
  return runner.get_bmc_result();
}

safety_checkert::resultt run_cbmc(const symbol_tablet &st,
    const goto_functionst &gf, cbmc_resultt &cbmc_result, const optionst &o)
{
  return run_cbmc(st, gf, cbmc_result,
      o.get_bool_option(CEGIS_KEEP_GOTO_PROGRAMS));
}
