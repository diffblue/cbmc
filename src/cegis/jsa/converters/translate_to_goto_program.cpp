/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/instructions/instruction_set_factory.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_genetic_synthesis.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/converters/replace_operators.h>
#include <cegis/jsa/converters/translate_to_goto_program.h>

#define PRED_SINGLE JSA_PREFIX "pred_opcode_"
#define PRED_FIRST JSA_PREFIX "pred_opcode_first_"
#define PRED_LAST JSA_PREFIX "pred_opcode_last_"
#define QUERY_SINGLE JSA_PREFIX "query_opcode_"
#define QUERY_FIRST JSA_PREFIX "query_opcode_first_"
#define QUERY_LAST JSA_PREFIX "query_opcode_last_"

namespace
{
instruction_sett get_instruction_set(const goto_functionst &gf,
    const char * const func, const char * const first,
    const char * const last, const char * const single)
{
  return extract_instruction_set(get_body(gf, func), first, last, single);
}

instruction_sett get_pred_instruction_set(const goto_functionst &gf)
{
  return get_instruction_set(gf, JSA_PRED_EXEC, PRED_FIRST, PRED_LAST, PRED_SINGLE);
}

instruction_sett get_query_instruction_set(const goto_functionst &gf)
{
  return get_instruction_set(gf, JSA_QUERY_EXEC, QUERY_FIRST, QUERY_LAST, QUERY_SINGLE);
}
}

void convert(goto_programt::instructionst &result, const jsa_programt &prog,
    const std::vector<__CPROVER_jsa_pred_instructiont> &solution)
{
  const instruction_sett instr_set(get_pred_instruction_set(prog.gf));
  assert(__CPROVER_JSA_NUM_PRED_INSTRUCTIONS == instr_set.size());
  copy_instructionst copy;
  for (const __CPROVER_jsa_pred_instructiont &instr : solution)
  {
    const instruction_sett::const_iterator it=instr_set.find(instr.opcode);
    assert(instr_set.end() != it);
    const size_t previous_size=result.size();
    copy(result, it->second);
    const goto_programt::targett new_instr(std::next(result.begin(), previous_size));
    replace_pred_ops(new_instr, result.end(), instr);
  }
  copy.finalize();
}

void convert(goto_programt::instructionst &result, const jsa_programt &prog,
    const std::vector<__CPROVER_jsa_query_instructiont> &solution)
{
  const instruction_sett instr_set(get_query_instruction_set(prog.gf));
  assert(!instr_set.empty());
  assert(!solution.empty());
  std::vector<__CPROVER_jsa_query_instructiont>::const_iterator instr=solution.begin();
  const __CPROVER_jsa_query_instructiont &prefix=*instr++;
  copy_instructionst copy;
  for (; instr != solution.end(); ++instr)
  {
    const instruction_sett::const_iterator it=instr_set.begin();
    const size_t previous_size=result.size();
    copy(result, it->second);
    const goto_programt::targett new_instr(std::next(result.begin(), previous_size));
    replace_query_ops(prog.st, new_instr, result.end(), *instr, prefix);
  }
  copy.finalize();
}

void convert(goto_programt::instructionst &result, const jsa_programt &prog,
    const std::vector<__CPROVER_jsa_invariant_instructiont> &solution)
{
  assert(!solution.empty());
  assert(solution.front().opcode == 0);
  result.push_back(goto_programt::instructiont());
  goto_programt::instructiont &instr=result.back();
  instr.source_location=jsa_builtin_source_location();
  instr.type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.function()=prog.st.lookup(JSA_INV_VERIFY_EXEC).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_user_heap(prog.gf)));
  args.push_back(address_of_exprt(get_queried_heap(prog.st)));
  instr.code=call;
}
