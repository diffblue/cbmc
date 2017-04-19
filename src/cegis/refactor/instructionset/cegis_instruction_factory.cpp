/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <numeric>

#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/processor_symbols.h>
#include <cegis/refactor/instructionset/cegis_instruction_factory.h>

namespace
{
class arithmetic_assignt
{
  const irep_idt id;
  const typet type;
public:
  arithmetic_assignt(const irep_idt &id, const typet &type) :
      id(id), type(type)
  {
  }

  goto_programt::targett operator()(const symbol_tablet &st,
      const std::string &func_name, goto_programt &body,
      const goto_programt::targett pos) const
  {
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=default_cegis_source_location();
    const dereference_exprt lhs(cegis_operand(st, func_name, type, 1));
    const dereference_exprt rhs(cegis_operand(st, func_name, type, 2));
    const binary_exprt result(lhs, id, rhs);
    pos->code=code_assignt(cegis_operand(st, func_name, type, 0), result);
    return pos;
  }
};

class arithmetic_instructionst
{
  const typet &type;
  const instruction_descriptiont::typest sig;
public:
  explicit arithmetic_instructionst(const typet &type) :
      type(type), sig( { type, type, type })
  {
  }

  instruction_descriptiont plus() const
  {
    return instruction_descriptiont(sig, arithmetic_assignt(ID_plus, type));
  }

  instruction_descriptiont minus() const
  {
    return instruction_descriptiont(sig, arithmetic_assignt(ID_minus, type));
  }

  instruction_descriptiont mult() const
  {
    return instruction_descriptiont(sig, arithmetic_assignt(ID_mult, type));
  }

  instruction_descriptiont div() const
  {
    return instruction_descriptiont(sig, arithmetic_assignt(ID_div, type));
  }
};

class assignt
{
  const typet type;
public:
  explicit assignt(const typet &type) :
      type(type)
  {
  }

  goto_programt::targett operator()(const symbol_tablet &st,
      const std::string &func_name, goto_programt &body,
      goto_programt::targett pos) const
  {
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=default_cegis_source_location();
    const dereference_exprt lhs(cegis_operand(st, func_name, type, 0));
    const dereference_exprt rhs(cegis_operand(st, func_name, type, 1));
    pos->code=code_assignt(lhs, rhs);
    return pos;
  }
};

instruction_descriptiont assign_desc(const typet &type)
{
  return instruction_descriptiont( { type, type }, assignt(type));
}

void insert(
    std::map<instruction_descriptiont::typest, instruction_descriptionst> &result,
    const instruction_descriptiont &instr)
{
  result[instr.signature].push_back(instr);
}
}

ordered_instructionst get_instructions_for_types(
    const cegis_operand_datat &signature)
{
  ordered_instructionst result;
  for(const cegis_operand_datat::value_type &typeWithSlots : signature)
  {
    const typet &type=typeWithSlots.first;
    if(!is_cegis_primitive(type)) continue; // TODO: Add support for class types
    const arithmetic_instructionst arith(type);
    insert(result, arith.plus());
    insert(result, arith.minus());
    insert(result, arith.mult());
    insert(result, arith.div());
    insert(result, assign_desc(type));
  }
  return result;
}

instruction_descriptionst::size_type num_instrs(
    const ordered_instructionst &instrs)
{
  return std::accumulate(instrs.begin(), instrs.end(), 0,
      [](const size_t count, const ordered_instructionst::value_type &instrs)
      { return count + instrs.second.size();});
}
