/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/bv_arithmetic.h>
#include <util/substitute.h>
#include <ansi-c/expr2c.h>
#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>
#include <cegis/refactor/learn/refactor_candidate_printer.h>

namespace
{
bool matches_opcode(const goto_programt::instructiont &instr,
    const mp_integer &opcode)
{
  if (!instr.is_goto() || ID_notequal != instr.guard.id()) return false;
  const notequal_exprt &guard=to_notequal_expr(instr.guard);
  return opcode == bv_arithmetict(guard.rhs()).to_integer();
}

void print_instr(messaget::mstreamt &os, const namespacet &ns,
    const goto_programt &body, const irep_idt &func_name,
    const struct_exprt &instr)
{
  std::ostringstream oss;
  const struct_exprt::operandst &ops=instr.operands();
  assert(!ops.empty());
  const mp_integer opcode(bv_arithmetict(ops.front()).to_integer());
  const goto_programt::instructionst &instrs=body.instructions;
  const goto_programt::const_targett end(instrs.end());
  goto_programt::const_targett first=std::next(
      std::find_if(instrs.begin(), end,
          [opcode](const goto_programt::instructiont &instr)
          { return matches_opcode(instr, opcode);}));
  const goto_programt::const_targett last=std::find_if(first, end,
      std::mem_fun_ref(&goto_programt::instructiont::is_goto));
  for (; first != last; ++first)
    body.output_instruction(ns, func_name, oss, first);
  std::string result(oss.str());
  for (size_t i=1; i < ops.size(); ++i)
  {
    std::string nd("*__CPROVER_cegis_variable_array_double[(program + i)->op_");
    nd+=std::to_string(i - 1);
    nd+=']';
    std::string replacement("op");
    replacement+=expr2c(ops[i], ns);
    substitute(result, nd, replacement);
  }
  os << result << messaget::endl;
}

void print_program(messaget::mstreamt &os, const namespacet &ns,
    const goto_programt &body, const irep_idt &func_name,
    const refactor_solutiont::value_type &prog)
{
  os << "  <prog>" << messaget::endl;
  os << "    <id>" << func_name << "</id>" << messaget::endl;
  os << "    <body>" << messaget::endl;
  for (const exprt &instr : prog.second.operands())
    print_instr(os, ns, body, func_name, to_struct_expr(instr));
  os << "    </body>" << messaget::endl;
  os << "  </prog>" << messaget::endl;
}
}

void print_refactor_candidate(messaget::mstreamt &os, const symbol_tablet &st,
    const goto_functionst &gf, const refactor_solutiont &candidate)
{
  os << "<refactor_candidate>" << messaget::endl;
  const namespacet ns(st);
  const goto_functionst::function_mapt &fmap=gf.function_map;
  for (const refactor_solutiont::value_type &entry : candidate)
  {
    std::string func(id2string(entry.first));
    remove_suffix(func, CEGIS_REFACTOR_PROG_SUFFIX);
    const goto_functionst::function_mapt::const_iterator it=fmap.find(func);
    assert(fmap.end() != it);
    assert(it->second.body_available());
    print_program(os, ns, it->second.body, it->first, entry);
  }
  os << "</refactor_candidate>" << messaget::eom;
}
