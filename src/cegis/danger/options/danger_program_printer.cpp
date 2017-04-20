/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program_printer.h>

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
      ns(prog.st), body_printer(get_entry_body(prog.gf)), os(os), func_count(0)
  {
  }

  void operator()(const goto_programt::instructionst &prog) const
  {
    /*goto_programt tmp;
    tmp.instructions=prog;
    tmp.compute_incoming_edges();
    tmp.compute_target_numbers();
    tmp.output(ns, "", os);*/
    // XXX: Debug
    for(goto_programt::const_targett it=prog.begin(); it != prog.end(); ++it)
      body_printer.output_instruction(ns, "", os, it);
    // XXX: Debug
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

void print_danger_program(messaget::mstreamt &os,
    const danger_programt &program, const danger_goto_solutiont &solution)
{
  const danger_goto_solutiont::nondet_choicest &x0=solution.x0_choices;
  const danger_goto_solutiont::danger_programst &progs=solution.danger_programs;
  if(x0.empty() && progs.empty()) return;
  os << "x0:" << messaget::endl;
  const expr_printert x0_printer(program, os);
  std::for_each(x0.begin(), x0.end(), x0_printer);
  os << "Programs:" << messaget::endl;
  const danger_program_printert prog_printer(program, os);
  std::for_each(progs.begin(), progs.end(), prog_printer);
  os << messaget::eom;
}
