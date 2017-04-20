/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/bv_arithmetic.h>

#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/value/program_individual.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/symex/learn/read_x0.h>

namespace
{
bool is_placeholder_of(const goto_programt::targett &x0,
    const goto_programt::const_targett &placeholder)
{
  const goto_programt::instructiont &placeholder_instr=*placeholder;
  if(goto_program_instruction_typet::DECL != placeholder_instr.type)
    return false;
  std::string placeholder_base(DANGER_X0_PLACEHOLDER_PREFIX);
  placeholder_base+=id2string(get_affected_variable(*x0));
  const std::string placeholder_name(get_cegis_meta_name(placeholder_base));
  return placeholder_name == id2string(get_affected_variable(placeholder_instr));
}

class extract_x0_choice
{
  danger_goto_solutiont &result;
  const goto_tracet &trace;
  goto_tracet::stepst::const_iterator current_step;
public:
  extract_x0_choice(danger_goto_solutiont &result, const goto_tracet &trace) :
      result(result), trace(trace)
  {
    assert(!trace.steps.empty());
    current_step=trace.steps.begin();
  }

  void operator()(const goto_programt::targett &x0)
  {
    const goto_tracet::stepst::const_iterator end(trace.steps.end());
    while(end != current_step && !is_placeholder_of(x0, current_step->pc))
      ++current_step;
    assert(end != current_step);
    result.x0_choices.push_back(current_step->full_lhs_value);
  }
};
}

void danger_read_x0(danger_goto_solutiont &result, const danger_programt &prog,
    const goto_tracet &trace)
{
  const goto_programt::targetst &x0=prog.x0_choices;
  const extract_x0_choice extract(result, trace);
  std::for_each(x0.begin(), x0.end(), extract);
}

void danger_read_x0(program_individualt &ind, const danger_programt &prog,
    const goto_tracet &trace)
{
  danger_goto_solutiont tmp;
  danger_read_x0(tmp, prog, trace);
  program_individualt::x0t &x0=ind.x0;
  for(const danger_goto_solutiont::nondet_choicest::value_type &choice : tmp.x0_choices)
  {
    const bv_arithmetict arith(choice);
    const mp_integer::llong_t value=arith.to_integer().to_long();
    x0.push_back(static_cast<program_individualt::x0t::value_type>(value));
  }
}
