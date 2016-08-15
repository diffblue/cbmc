#include <cegis/cegis-util/program_helper.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_solution_printer.h>

namespace
{
void print_instructions(messaget::mstreamt &os, const jsa_programt &program,
    const goto_programt::instructionst &instrs)
{
  const goto_programt &prog=get_entry_body(program.gf);
  const namespacet ns(program.st);
  for (goto_programt::const_targett it=instrs.begin(); it != instrs.end(); ++it)
    prog.output_instruction(ns, "", os, it);
}
}

void print_jsa_solution(messaget::mstreamt &os, const jsa_programt &program,
    const jsa_solutiont &solution)
{
  if (solution.query.empty())
  {
    os << "<jsa_solution />" << messaget::endl << messaget::eom;
    return;
  }
  os << "<jsa_solution>" << messaget::endl;
  os << "  <predicates>" << messaget::endl;
  const jsa_solutiont::predicatest &predicates=solution.predicates;
  for (const goto_programt::instructionst &predicate : predicates)
    print_instructions(os, program, predicate);

  os << "  </predicates>" << messaget::endl;

  os << "  <query>" << messaget::endl;
  print_instructions(os, program, solution.query);
  os << "  </query>" << messaget::endl;
  os << "  <invariant>" << messaget::endl;
  print_instructions(os, program, solution.invariant);
  os << "  </invariant>" << messaget::endl;
  os << "</jsa_solution>" << messaget::endl << messaget::eom;
}
