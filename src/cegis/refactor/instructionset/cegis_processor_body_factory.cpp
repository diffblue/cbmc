#include <algorithm>
#include <functional>

#include <util/arith_tools.h>
#include <util/expr_util.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/processor_symbols.h>
#include <cegis/refactor/instructionset/cegis_instruction_factory.h>
#include <cegis/refactor/instructionset/cegis_processor_body_factory.h>

#define NUM_PRIMITIVE_OPERANDS 3u

namespace
{
size_t cegis_max_operands(const typet &type)
{
  if (!is_cegis_primitive(type)) return 0;  // TODO: Add support for class types
  return NUM_PRIMITIVE_OPERANDS;
}
}

size_t cegis_max_operands(const cegis_operand_datat &slots)
{
  size_t max=0;
  for (const cegis_operand_datat::value_type &slot : slots)
    max=std::max(max, cegis_max_operands(slot.first));
  return max;
}

namespace
{
class body_factoryt
{
  const cegis_operand_datat &slots;
  const ordered_instructionst &ordered_instructions;
  symbol_tablet &st;
  goto_programt &body;
  const std::string &func_name;
  const source_locationt loc;
  const goto_programt::targett first;
  const goto_programt::targett last;
  goto_programt::targett pos;
  goto_programt::targett loop_head;
  goto_programt::targett last_case;
  goto_programt::targett switch_end;

  std::string meta_name(const std::string &base_name)
  {
    return get_local_meta_name(func_name, base_name);
  }

  void src_loc(const goto_programt::targett pos)
  {
    pos->source_location=loc;
    pos->function=func_name;
  }

  goto_programt::targett dead(const std::string &name)
  {
    goto_programt::targett pos=body.insert_after(this->pos);
    pos->type=goto_program_instruction_typet::DEAD;
    src_loc(pos);
    const std::string symbol_name(meta_name(name));
    pos->code=code_deadt(st.lookup(symbol_name).symbol_expr());
    return pos;
  }

  void decl(const std::string &name, const typet &type)
  {
    pos=declare_local_meta_variable(st, func_name, body, pos, name, type);
    dead(name);
  }

  void decl(const std::string &name, const exprt &value)
  {
    decl(name, value.type());
    pos=cegis_assign_local_variable(st, body, pos, func_name, name, value);
  }

  void add_goto(const exprt &guard, const goto_programt::targett &target)
  {
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    src_loc(pos);
    pos->set_target(target);
    pos->guard=guard;
  }

  goto_programt::targett add_conditional_instr_goto(const size_t opcode,
      const irep_idt &relation)
  {
    if (last == switch_end)
    {
      switch_end=body.insert_after(pos);
      switch_end->type=goto_program_instruction_typet::SKIP;
      switch_end->source_location=loc;
    }
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    src_loc(pos);
    const constant_exprt rhs(from_integer(opcode, cegis_size_type()));
    const member_exprt lhs(cegis_opcode(st, func_name));
    pos->guard=binary_relation_exprt(lhs, relation, rhs);
    if (last != last_case) last_case->set_target(pos);
    last_case=pos;
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::SKIP;
    src_loc(pos);
    const goto_programt::targett result(pos);
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    src_loc(pos);
    pos->set_target(switch_end);
    return result;
  }

  void finalise_conditional_instr_gotos()
  {
    assert(last != last_case);
    last_case->set_target(switch_end);
    last_case=last;
    assert(last != switch_end);
    pos=switch_end;
    switch_end=last;
  }

  void assume_less(const goto_programt::targett pos, const exprt &lhs,
      const size_t value)
  {
    const constant_exprt rhs(from_integer(value, cegis_opcode_type()));
    pos->type=goto_program_instruction_typet::ASSUME;
    src_loc(pos);
    pos->guard=binary_relation_exprt(lhs, ID_lt, rhs);
  }
public:
  body_factoryt(const cegis_operand_datat &slots,
      const ordered_instructionst &ordered_instructions, symbol_tablet &st,
      goto_programt &body, const std::string &func_name) :
      slots(slots), ordered_instructions(ordered_instructions), st(st), body(
          body), func_name(func_name), loc(default_cegis_source_location()), first(
          body.add_instruction(SKIP)), last(body.instructions.end()), pos(
          first), loop_head(last), last_case(last), switch_end(last)
  {
  }

  ~body_factoryt()
  {
    body.instructions.erase(first);
  }

  void declare_instruction_loop_head()
  {
    decl(CEGIS_PROC_INSTR_INDEX, gen_zero(cegis_size_type()));
    const member_exprt opcode(cegis_opcode(st, func_name));
    const size_t size(num_instrs(ordered_instructions));
    assume_less(pos=body.insert_after(pos), opcode, size);
    loop_head=pos;
  }

  void finish_instruction_loop()
  {
    pos=std::prev(body.instructions.end(), 2);
    while (goto_program_instruction_typet::DEAD == pos->type)
      pos=std::prev(pos);
    const char * const base_idx_name=CEGIS_PROC_INSTR_INDEX;
    const std::string idx(meta_name(base_idx_name));
    const symbol_exprt idx_expr(st.lookup(idx).symbol_expr());
    const plus_exprt rhs(idx_expr, gen_one(idx_expr.type()));
    cegis_assign_local_variable(st, body, pos, func_name, base_idx_name, rhs);
    pos=std::prev(body.instructions.end(), 2);
    const std::string index(meta_name(CEGIS_PROC_INSTR_INDEX));
    const symbol_exprt index_expr(st.lookup(index).symbol_expr());
    const std::string sz(meta_name(CEGIS_PROC_PROGRAM_SIZE_PARAM_ID));
    const symbol_exprt sz_expr(st.lookup(sz).symbol_expr());
    const binary_relation_exprt guard(index_expr, ID_lt, sz_expr);
    add_goto(guard, std::next(loop_head));
  }

  void add_signature_assumptions()
  {
    size_t opcode=0;
    for (const ordered_instructionst::value_type &entry : ordered_instructions)
    {
      const ordered_instructionst::value_type::second_type &instrs=entry.second;
      opcode+=instrs.size();
      goto_programt::targett pos=add_conditional_instr_goto(opcode, ID_ge);
      const ordered_instructionst::value_type::first_type &sig=entry.first;
      for (size_t op=0; op < sig.size(); ++op)
      {
        if (SKIP != pos->type) pos=body.insert_after(pos);
        const cegis_operand_datat::const_iterator it=slots.find(sig[op]);
        assert(slots.end() != it);
        const member_exprt operand_id(cegis_operand_id(st, func_name, op));
        assume_less(pos, operand_id, it->second);
      }
    }
    finalise_conditional_instr_gotos();
  }

  void execute_instructions()
  {
    const irep_idt id(ID_notequal);
    size_t opc=0;
    for (const ordered_instructionst::value_type &entry : ordered_instructions)
      for (const instruction_descriptiont &instr : entry.second)
      {
        const goto_programt::targett it=add_conditional_instr_goto(opc++, id);
        instr(st, func_name, body, it);
      }
    finalise_conditional_instr_gotos();
  }
};
}

void generate_processor_body(symbol_tablet &st, goto_programt &body,
    const std::string &name, const cegis_operand_datat &slots)
{
  const ordered_instructionst instructions(get_instructions_for_types(slots));
  if (!slots.empty())
  {
    body_factoryt factory(slots, instructions, st, body, name);
    factory.declare_instruction_loop_head();
    factory.add_signature_assumptions();
    factory.execute_instructions();
    factory.finish_instruction_loop();
  }
  body.add_instruction(goto_program_instruction_typet::END_FUNCTION);
  body.compute_loop_numbers();
  body.update();
}
