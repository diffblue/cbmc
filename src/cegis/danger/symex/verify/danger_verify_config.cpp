/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <cegis/value/assignments_printer.h>
#include <cegis/wordsize/restrict_bv_size.h>
#include <cegis/invariant/symex/verify/extract_counterexample.h>
#include <cegis/invariant/symex/verify/insert_constraint.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/symex/verify/insert_candidate.h>
#include <cegis/danger/symex/verify/danger_verify_config.h>

danger_verify_configt::danger_verify_configt(const danger_programt &program) :
    original_program(program), limit_ce(false), max_ce_width(0u)
{
}

danger_verify_configt::~danger_verify_configt()
{
}

void danger_verify_configt::process(const candidatet &candidate)
{
  program=original_program;
  quantifiers.clear();
  const danger_constraint constraint(program.use_ranking);
  invariant_insert_constraint(quantifiers, program, std::cref(constraint));
  danger_insert_candidate(program, candidate);
  goto_functionst &gf=program.gf;
  if(limit_ce) restrict_bv_size(program.st, gf, max_ce_width);
  gf.update();
}

const symbol_tablet &danger_verify_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &danger_verify_configt::get_goto_functions() const
{
  return program.gf;
}

goto_functionst &danger_verify_configt::get_goto_functions()
{
  return program.gf;
}

void danger_verify_configt::convert(counterexamplest &counterexamples,
    const goto_tracet &trace)
{
  counterexamples.push_back(counterexamplet());
  invariant_extract_counterexample(counterexamples.back(), trace, quantifiers);
}

size_t danger_verify_configt::get_number_of_loops() const
{
  return original_program.loops.size();
}

exprt::operandst danger_verify_configt::get_loop_guards() const
{
  exprt::operandst loop_guards;
  const danger_programt::loopst &loops=original_program.loops;
  std::transform(loops.begin(), loops.end(), std::back_inserter(loop_guards),
      [](const danger_programt::loopt &loop)
      { return loop.guard;});
  return loop_guards;
}

void danger_verify_configt::set_max_ce_width(const size_t size)
{
  limit_ce=true;
  max_ce_width=size;
}

void danger_verify_configt::show_counterexample(messaget::mstreamt &os,
    const counterexamplet &counterexample) const
{
  os << "<danger_counterexample>" << messaget::endl;
  print_assignments(os, get_symbol_table(), counterexample);
  os << "</danger_counterexample>" << messaget::endl << messaget::eom;
}
