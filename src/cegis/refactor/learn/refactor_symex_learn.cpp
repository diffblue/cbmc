/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/string_helper.h>
#include <cegis/learn/constraint_helper.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>
#include <cegis/refactor/learn/instrument_counterexamples.h>
#include <cegis/refactor/learn/refactor_candidate_printer.h>
#include <cegis/refactor/learn/refactor_symex_learn.h>

refactor_symex_learnt::refactor_symex_learnt(
    const refactor_programt &original_program) :
    original_program(original_program)
{
}

void refactor_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  for (const irep_idt &program : current_program.programs)
  {
    symbolt &symbol=st.lookup(program);
    assign_in_cprover_init(gf, symbol, side_effect_expr_nondett(symbol.type));
  }
  transform_asserts_to_assumes(current_program.gf);
  instrument_counterexamples(current_program, counterexamples);
}

const symbol_tablet &refactor_symex_learnt::get_symbol_table() const
{
  return current_program.st;
}

const goto_functionst &refactor_symex_learnt::get_goto_functions() const
{
  return current_program.gf;
}

void refactor_symex_learnt::set_word_width(
    const size_t word_width_in_bits) const
{
}

namespace
{
class handle_assignt
{
  const std::set<irep_idt> &progs;
  refactor_symex_learnt::candidatet &candidate;
public:
  handle_assignt(const std::set<irep_idt> &programs,
      refactor_symex_learnt::candidatet &candidate) :
      progs(programs), candidate(candidate)
  {
  }

  void operator()(const goto_trace_stept &step) const
  {
    if (!step.is_assignment()) return;
    const std::string &v=id2string(step.lhs_object.get_identifier());
    const auto it=std::find_if(progs.begin(), progs.end(),
        std::bind(starts_with, v, std::bind(id2string, std::placeholders::_1)));
    if (progs.end() == it || !ends_with(v, CEGIS_REFACTOR_PROG_SUFFIX)) return;
    const array_exprt &value=to_array_expr(step.full_lhs_value);
    assert(candidate.insert(std::make_pair(v, value)).second);
  }
};
}

void refactor_symex_learnt::convert(candidatet &current_candidate,
    const goto_tracet &trace, const size_t max_solution_size) const
{
  current_candidate.clear();
  const goto_tracet::stepst &steps=trace.steps;
  const handle_assignt handle(current_program.programs, current_candidate);
  std::for_each(steps.begin(), steps.end(), handle);
}

void refactor_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &c) const
{
  print_refactor_candidate(os, current_program.st, current_program.gf, c);
}
