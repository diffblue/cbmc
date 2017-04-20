/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/remove_returns.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/value/jsa_solution_printer.h>
#include <cegis/jsa/preprocessing/add_synthesis_library.h>
#include <cegis/jsa/constraint/jsa_constraint_factory.h>
#include <cegis/jsa/learn/insert_counterexample.h>
#include <cegis/jsa/learn/insert_predicates_and_queries.h>
#include <cegis/jsa/learn/instrument_pred_ops.h>
#include <cegis/jsa/learn/execute_jsa_programs.h>
#include <cegis/jsa/learn/extract_candidate.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>

jsa_symex_learnt::jsa_symex_learnt(const jsa_programt &program) :
    original_program(program)
{
}

void jsa_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  program=original_program;
  const goto_programt::targetst pred_ops(collect_pred_ops(program));
  // add_jsa_library(program, max_solution_size, pred_ops);
  instrument_pred_ops(program, pred_ops, op_ids, const_op_ids);
  insert_jsa_constraint(program, true);
  insert_counterexamples(program, counterexamples);
  declare_jsa_predicates(program, max_solution_size);
  declare_jsa_query(program, max_solution_size);
  declare_jsa_invariant(program, max_solution_size);
  execute_jsa_learn_programs(program);
  remove_returns(program.st, program.gf);
  program.gf.update();
}

void jsa_symex_learnt::process(const size_t max_solution_size)
{
  const namespacet ns(original_program.st);
  counterexamplest counterexamples(1);
  counterexamplet &counterexample=counterexamples.front();
  for(const goto_programt::targett &pos : original_program.counterexample_locations)
  {
    assert(pos->labels.size() == 1u);
    const irep_idt &key=pos->labels.front();
    const typet &type=get_affected_type(*pos);
    const source_locationt &loc=pos->source_location;
    const exprt value(zero_initializer(type, loc, ns));
    counterexample.insert(std::make_pair(key, value));
  }
  process(counterexamples, max_solution_size);
}

void jsa_symex_learnt::set_word_width(const size_t word_width_in_bits)
{
  // XXX: Unsupported
}

void jsa_symex_learnt::convert(candidatet &result, const goto_tracet &trace,
    const size_t max_sz)
{
  result.clear();
  extract_jsa_candidate(result, program, trace, const_op_ids, op_ids, max_sz);
  result.max_size=max_sz;
}

const symbol_tablet &jsa_symex_learnt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &jsa_symex_learnt::get_goto_functions() const
{
  return program.gf;
}

const jsa_programt &jsa_symex_learnt::get_jsa_program() const
{
  return program;
}

void jsa_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  print_jsa_solution(os, program, candidate, op_ids, const_op_ids);
}

std::function<size_t()> jsa_symex_learnt::get_pred_ops_count() const
{
  return [this]()
  { return op_ids.size();};
}

std::function<size_t()> jsa_symex_learnt::get_const_pred_ops_count() const
{
  return [this]()
  { return const_op_ids.size();};
}
