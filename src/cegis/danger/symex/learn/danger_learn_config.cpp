#include <algorithm>

#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/danger_library.h>
#include <cegis/danger/symex/learn/add_programs_to_learn.h>
#include <cegis/danger/symex/learn/add_counterexamples.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/learn/danger_learn_config.h>

danger_learn_configt::danger_learn_configt(const danger_programt &program) :
    original_program(program)
{
}

danger_learn_configt::~danger_learn_configt()
{
}

void danger_learn_configt::process(const counterexamplest &counterexamples,
    const size_t max_solution_size)
{
  program=original_program;
  var_ids.clear();
  const size_t num_consts=get_danger_variable_ids(program.st, var_ids);
  const size_t num_vars=var_ids.size();
  null_message_handlert msg;
  add_danger_library(program, msg, num_vars, num_consts, max_solution_size);
  danger_add_variable_refs(program, var_ids, max_solution_size);
  danger_add_programs_to_learn(program, max_solution_size);
  danger_add_learned_counterexamples(program, counterexamples);
}

const symbol_tablet &danger_learn_configt::get_symbol_table() const
{
  return program.st;
}

const goto_functionst &danger_learn_configt::get_goto_functions() const
{
  return program.gf;
}

void danger_learn_configt::danger_learn_configt::convert(candidatet &candidate,
    const class goto_tracet &trace, const size_t max_solution_size)
{
  candidate.danger_programs.clear();
  candidate.x0_choices.clear();
  create_danger_solution(candidate, program, trace, var_ids, max_solution_size);
}

namespace
{
class danger_program_printert
{
  const namespacet ns;
  const goto_programt &body_printer;
  messaget::mstreamt &os;
  size_t func_count;
public:
  danger_program_printert(const danger_programt &prog, messaget::mstreamt &os) :
      ns(prog.st), body_printer(get_danger_body(prog.gf)), os(os), func_count(0)
  {
  }

  void operator()(const goto_programt::instructionst &prog) const
  {
    for (goto_programt::const_targett it=prog.begin(); it != prog.end(); ++it)
      body_printer.output_instruction(ns, "", os, it);
  }

  void operator()(const danger_goto_solutiont::danger_programt &prog)
  {
    const danger_program_printert &print=*this;
    os << "Invariant " << func_count << ": " << messaget::endl;
    print(prog.invariant);
    os << "Ranking " << func_count << ": " << messaget::endl;
    print(prog.ranking);
    os << "Skolem " << func_count++ << ": " << messaget::endl;
    print(prog.skolem);
  }
};

class expr_printert
{
  const namespacet ns;
  goto_programt::targetst::const_iterator current_choice;
  messaget::mstreamt &os;
public:
  expr_printert(const danger_programt &prog, messaget::mstreamt &os) :
      ns(prog.st), current_choice(prog.x0_choices.begin()), os(os)
  {
  }

  void operator()(const exprt &expr)
  {
    os << get_affected_variable(**current_choice++) << "=";
    os << from_expr(ns, "", expr) << messaget::endl;
  }
};
}

void danger_learn_configt::show_candidate(messaget::mstreamt &os,
    const candidatet &candidate)
{
  os << "x0:" << messaget::endl;
  const candidatet::nondet_choicest &x0=candidate.x0_choices;
  const expr_printert x0_printer(program, os);
  std::for_each(x0.begin(), x0.end(), x0_printer);
  os << "Programs:" << messaget::endl;
  const candidatet::danger_programst &progs=candidate.danger_programs;
  const danger_program_printert prog_printer(program, os);
  std::for_each(progs.begin(), progs.end(), prog_printer);
  os << messaget::eom;
}
