/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <cegis/constant/literals_collector.h>
#include <cegis/cegis-util/program_helper.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_solution_printer.h>

namespace
{
void print(messaget::mstreamt &os, const pred_op_idst &op_ids)
{
  for(const pred_op_idst::value_type &op : op_ids)
  {
    os << "      <op><id>" << op.first << "</id>";
    const irep_idt &id=op.second.get_identifier();
    os << "<name>" << id << "</name></op>" << messaget::endl;
  }
}

void print_consts(messaget::mstreamt &os, const jsa_programt &prog)
{
  const symbol_tablet &st=prog.st;
  const goto_functionst &gf=prog.gf;
  const std::vector<constant_exprt> values(collect_integer_literals(st, gf));
  os << "  <consts>" << messaget::endl;
  size_t index=0;
  for(const constant_exprt &expr : values)
  {
    mp_integer literal;
    to_integer(expr, literal);
    os << "    <const><id>" << index++ << "</id>";
    const mp_integer::llong_t value=literal.to_long();
    os << "<value>" << value << "</value></const>" << messaget::endl;
  }
  os << "  </consts>" << messaget::endl;
}

void print_instructions(messaget::mstreamt &os, const jsa_programt &program,
    const goto_programt::instructionst &instrs)
{
  const goto_programt &prog=get_entry_body(program.gf);
  const namespacet ns(program.st);
  for(goto_programt::const_targett it=instrs.begin(); it != instrs.end(); ++it)
    prog.output_instruction(ns, "", os, it);
}
}

void print_jsa_solution(messaget::mstreamt &os, const jsa_programt &program,
    const jsa_solutiont &solution, const pred_op_idst &op_ids,
    const pred_op_idst &const_op_ids)
{
  if(solution.query.empty() || program.st.symbols.empty())
  {
    os << "<jsa_solution />" << messaget::endl << messaget::eom;
    return;
  }
  os << "<jsa_solution>" << messaget::endl;
  print_consts(os, program);
  os << "  <variables>" << messaget::endl;
  os << "    <mutable>" << messaget::endl;
  print(os, op_ids);
  os << "    </mutable>" << messaget::endl;
  os << "    <const>" << messaget::endl;
  print(os, const_op_ids);
  os << "    </const>" << messaget::endl;
  os << "  </variables>" << messaget::endl;
  os << "  <predicates>" << messaget::endl;
  const jsa_solutiont::predicatest &predicates=solution.predicates;
  for(const goto_programt::instructionst &predicate : predicates)
  {
    os << "    <predicate>" << messaget::endl;
    print_instructions(os, program, predicate);
    os << "    </predicate>" << messaget::endl;
  }
  os << "  </predicates>" << messaget::endl;
  os << "  <query>" << messaget::endl;
  print_instructions(os, program, solution.query);
  os << "  </query>" << messaget::endl;
  os << "  <invariant>" << messaget::endl;
  print_instructions(os, program, solution.invariant);
  os << "  </invariant>" << messaget::endl;
  os << "</jsa_solution>" << messaget::endl << messaget::eom;
}
