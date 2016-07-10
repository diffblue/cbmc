#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_solution_printer.h>

void print_danger_program(messaget::mstreamt &os, const jsa_programt &program,
    const jsa_solutiont &solution)
{
  const jsa_solutiont::predicatest &predicates=solution.predicates;
  const goto_programt::instructionst &query=solution.query;
  for (const goto_programt::instructiont &instr : query)
  {

  }
}
