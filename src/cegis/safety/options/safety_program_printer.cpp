/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/value/safety_goto_solution.h>
#include <cegis/safety/options/safety_program_printer.h>

namespace
{
class program_printert
{
  const namespacet ns;
  const goto_programt &body_printer;
  messaget::mstreamt &os;
  size_t func_count;
public:
  program_printert(const safety_programt &prog, messaget::mstreamt &os) :
      ns(prog.st), body_printer(get_entry_body(prog.gf)), os(os), func_count(0)
  {
  }

  void operator()(const goto_programt::instructionst &prog)
  {
    os << "Invariant " << func_count++ << ": " << messaget::endl;
    for(goto_programt::const_targett it=prog.begin(); it != prog.end(); ++it)
      body_printer.output_instruction(ns, "", os, it);
  }
};
}

void print_safety_program(messaget::mstreamt &os,
    const safety_programt &program, const safety_goto_solutiont &solution)
{
  os << "Programs:" << messaget::endl;
  const program_printert prog_printer(program, os);
  std::for_each(solution.begin(), solution.end(), prog_printer);
  os << messaget::eom;
}
