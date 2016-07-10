#include <goto-programs/remove_returns.h>

#include <cegis/jsa/preprocessing/add_synthesis_library.h>
#include <cegis/jsa/learn/insert_counterexample.h>
#include <cegis/jsa/learn/insert_predicates_and_queries.h>
#include <cegis/jsa/learn/instrument_pred_ops.h>
#include <cegis/jsa/learn/execute_jsa_programs.h>
#include <cegis/jsa/learn/extract_candidate.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>

// XXX: Debug
#include <iostream>
#include <goto-instrument/dump_c.h>
// XXX: Debug

jsa_symex_learnt::jsa_symex_learnt(const jsa_programt &program) :
    original_program(program)
{
}

jsa_symex_learnt::~jsa_symex_learnt()
{
}

void jsa_symex_learnt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  program=original_program;
  const goto_programt::targetst pred_ops(collect_pred_ops(program));
  //add_jsa_library(program, max_solution_size, pred_ops);
  instrument_pred_ops(program, pred_ops, op_ids, const_op_ids);
  insert_counterexamples(program, counterexamples);
  declare_jsa_predicates(program, max_solution_size);
  declare_jsa_query(program, max_solution_size);
  declare_jsa_invariant(program, max_solution_size);
  execute_jsa_learn_programs(program);
  remove_returns(program.st, program.gf);
  program.gf.update();

  // XXX: Debug
  std::cout << "<num_ces>" << counterexamples.size() << "</num_ces>" << std::endl;
  // XXX: Debug
  program.gf.function_map.erase("main");
  const namespacet ns(program.st);
  std::cout << "<jsa_symex_learnt>" << std::endl;
  dump_c(program.gf, true, ns, std::cout);
  std::cout << "</jsa_symex_learnt>" << std::endl;
  // XXX: Debug
  // XXX: Debug
  //const namespacet ns(program.st);
  std::cout << "<jsa_symex_learn_program>" << std::endl;
  program.gf.output(ns, std::cout);
  std::cout << "</jsa_symex_learn_program>" << std::endl;
  // XXX: Debug
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

void jsa_symex_learnt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  // TODO: Implement (Java 8 Stream query formatter?)
  os << "TODO: print candidate" << messaget::eom;
}
