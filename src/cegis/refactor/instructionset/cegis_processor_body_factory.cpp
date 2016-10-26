#include <ansi-c/expr2c.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/cegis_processor_body_factory.h>

#define OPERAND_ID_MEMBER_NAME_PREFIX "op_"
#define OPERAND_TMP_RESULT_PREFIX "result_op_"
#define INSTR_INDEX "i"

std::string cegis_operand_base_name(const size_t op)
{
  std::string name(OPERAND_ID_MEMBER_NAME_PREFIX);
  return name+=std::to_string(op);
}

#define VARIABLE_ARRAY_PREFIX CEGIS_PREFIX "variable_array_"

std::string cegis_operand_array_name(const symbol_tablet &st, const typet &type)
{
  std::string result(VARIABLE_ARRAY_PREFIX);
  return result+=type2c(type, namespacet(st));
}

#define NUM_PRIMITIVE_OPERANDS 2u

namespace
{
bool is_primitive(const typet &type)
{
  const irep_idt &id=type.id();
  return ID_c_bool == id || ID_floatbv == id || ID_unsignedbv == id
      || ID_signedbv == id;
}

size_t cegis_max_operands(const typet &type)
{
  if (!is_primitive(type))
  assert(!"Class type operand generation not supported.");
  return NUM_PRIMITIVE_OPERANDS;
}
}

size_t cegis_max_operands(const cegis_operand_datat &slots)
{
  size_t max=0;
  for (const std::pair<typet, size_t> &slot : slots)
    max=std::max(max, cegis_max_operands(slot.first));
  return max;
}

#define NUM_PRIMITIVE_OPCODES 4u

namespace
{
size_t get_num_instructions(const typet &type)
{
  if (!is_primitive(type))
  assert(!"Class type operand generation not supported.");
  return NUM_PRIMITIVE_OPCODES;
}

std::string get_tmp_op(const symbol_tablet &st, const size_t op,
    const typet &type)
{
  std::string result(OPERAND_ID_MEMBER_NAME_PREFIX);
  result+=std::to_string(op);
  result+='_';
  return result+=type2c(type, namespacet(st));
}

std::string get_tmp_result_op(const symbol_tablet &st, const typet &type)
{
  std::string result(OPERAND_TMP_RESULT_PREFIX);
  return result+=type2c(type, namespacet(st));
}

class body_factoryt
{
  symbol_tablet &st;
  goto_programt &body;
  const std::string &func_name;
  const cegis_operand_datat &slots;
  const goto_programt::targett end;
  goto_programt::targett dummy;
  goto_programt::targett loop_head;
  goto_programt::targett last_case;
  goto_programt::targett switch_end;
  goto_programt::targett pos;

  std::string meta_name(const std::string &base_name)
  {
    return get_local_meta_name(func_name, base_name);
  }

  goto_programt::targett dead(const std::string &name)
  {
    goto_programt::targett pos=body.insert_after(this->pos);
    pos->type=goto_program_instruction_typet::DEAD;
    pos->source_location=default_cegis_source_location();
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

  void decl_instr_member(const std::string &name)
  {
    const std::string prog(meta_name(CEGIS_PROC_PROGRAM_PARAM_ID));
    const symbol_exprt prog_expr(st.lookup(prog).symbol_expr());
    const std::string index(meta_name(INSTR_INDEX));
    const symbol_exprt index_expr(st.lookup(index).symbol_expr());
    const index_exprt instr(prog_expr, index_expr); // TODO: Might fail due to pointer type
    const member_exprt member(instr, name, cegis_opcode_type());
    decl(name, member);
  }

  void add_goto(const exprt &guard, const goto_programt::targett &target)
  {
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=default_cegis_source_location();
    pos->set_target(target);
    pos->guard=guard;
  }

  goto_programt::targett add_conditional_instr_goto(const size_t opcode,
      const irep_idt &relation)
  {
    const source_locationt loc(default_cegis_source_location());
    if (end == switch_end)
    {
      switch_end=body.insert_after(pos);
      switch_end->type=goto_program_instruction_typet::SKIP;
      switch_end->source_location=loc;
    }
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=loc;
    const constant_exprt rhs(from_integer(opcode, cegis_size_type()));
    const std::string name(meta_name(CEGIS_PROC_OPCODE_MEMBER_NAME));
    const symbol_exprt lhs(st.lookup(name).symbol_expr());
    pos->guard=binary_relation_exprt(lhs, relation, rhs);
    if (end != last_case) last_case->set_target(pos);
    last_case=pos;
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::SKIP;
    pos->source_location=loc;
    const goto_programt::targett result(pos);
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=loc;
    pos->set_target(switch_end);
    return result;
  }

  void finalise_conditional_instr_gotos()
  {
    assert(end != last_case);
    last_case->set_target(switch_end);
    last_case=end;
    assert(end != switch_end);
    pos=switch_end;
    switch_end=end;
  }

  void execute_instruction(const goto_programt::targett pos, const typet &t,
      const size_t op)
  {
    if (!is_primitive(t))
    assert(!"Class type operand generation not supported.");
    pos->type=goto_program_instruction_typet::ASSIGN;
    const symbol_exprt res(get_tmp_result_expr(t));
    pos->code=code_assignt(res, nil_exprt());
    code_assignt &assign=to_code_assign(pos->code);
    const symbol_exprt lhs(get_tmp_op_expr(t, 0));
    const symbol_exprt rhs(get_tmp_op_expr(t, 1));
    switch (op)
    {
    case 0:
      assign.rhs()=plus_exprt(lhs, rhs);
      break;
    case 1:
      assign.rhs()=minus_exprt(lhs, rhs);
      break;
    case 2:
      assign.rhs()=mult_exprt(lhs, rhs);
      break;
    default:
      const goto_programt::targett assume(body.insert_before(pos));
      assume->source_location=pos->source_location;
      assume->type=goto_program_instruction_typet::ASSUME;
      assume->guard=notequal_exprt(rhs, gen_zero(t));
      assign.rhs()=div_exprt(lhs, rhs);
      break;
    }
  }

  symbol_exprt get_tmp_op_expr(const typet &type, const size_t index)
  {
    const std::string base_name(get_tmp_op(st, index, type));
    const std::string name(meta_name(base_name));
    return st.lookup(name).symbol_expr();
  }

  symbol_exprt get_tmp_result_expr(const typet &type)
  {
    const std::string base_name(get_tmp_result_op(st, type));
    const std::string name(meta_name(base_name));
    return st.lookup(name).symbol_expr();
  }

  dereference_exprt get_variable_array_element(const typet &type,
      const std::string index_var_base_name)
  {
    const std::string name(meta_name(index_var_base_name));
    const symbol_exprt index(st.lookup(name).symbol_expr());
    const std::string array_name(cegis_operand_array_name(st, type));
    const symbol_exprt array(st.lookup(array_name).symbol_expr());
    return dereference_exprt(index_exprt(array, index));
  }

  dereference_exprt get_op_variable_array_element(const typet &type,
      const size_t op_id)
  {
    return get_variable_array_element(type, cegis_operand_base_name(op_id));
  }

  dereference_exprt get_result_variable_array_element(const typet &type)
  {
    const std::string base_name(get_tmp_result_op(st, type));
    return get_variable_array_element(type, base_name);
  }
public:
  body_factoryt(symbol_tablet &st, goto_programt &body, const std::string &name,
      const cegis_operand_datat &slots) :
      st(st), body(body), func_name(name), slots(slots), end(
          body.instructions.end()), dummy(body.add_instruction(SKIP)), last_case(
          end), switch_end(end)
  {
    pos=dummy;
  }

  ~body_factoryt()
  {
    body.instructions.erase(dummy);
  }

  void declare_instruction_properties()
  {
    decl(INSTR_INDEX, gen_zero(cegis_size_type()));
    decl_instr_member(CEGIS_PROC_OPCODE_MEMBER_NAME);
    loop_head=std::prev(pos);
    const size_t global_max_operands=cegis_max_operands(slots);
    for (size_t i=0; i < global_max_operands; ++i)
      decl_instr_member(cegis_operand_base_name(i));
  }

  void declare_temp_vars()
  {
    for (const std::pair<typet, size_t> &slot : slots)
    {
      const typet &type=slot.first;
      const size_t max_operands=cegis_max_operands(type);
      for (size_t i=0; i < max_operands; ++i)
        decl(get_tmp_op(st, i, type), type);
      decl(get_tmp_result_op(st, type), type);
    }
  }

  void init_temp_vars()
  {
    const source_locationt loc(default_cegis_source_location());
    size_t opcode=0;
    for (const std::pair<typet, size_t> &slot : slots)
    {
      const typet &type=slot.first;
      opcode+=get_num_instructions(type);
      assert(opcode);
      const size_t max_operands=cegis_max_operands(type);
      assert(max_operands);
      goto_programt::targett pos=add_conditional_instr_goto(opcode, ID_ge);
      for (size_t i=0; i < max_operands; ++i)
      {
        if (!pos->code.get_statement().empty()) pos=body.insert_after(pos);
        pos->type=goto_program_instruction_typet::ASSIGN;
        pos->source_location=loc;
        const symbol_exprt lhs(get_tmp_op_expr(type, i));
        const dereference_exprt rhs(get_op_variable_array_element(type, i));
        pos->code=code_assignt(lhs, rhs);
      }
    }
    finalise_conditional_instr_gotos();
  }

  void assign_result_vars()
  {
    const source_locationt loc(default_cegis_source_location());
    size_t opcode=0;
    for (const std::pair<typet, size_t> &slot : slots)
    {
      const typet &type=slot.first;
      opcode+=get_num_instructions(type);
      assert(opcode);
      const size_t max_operands=cegis_max_operands(type);
      assert(max_operands);
      goto_programt::targett pos=add_conditional_instr_goto(opcode, ID_ge);
      pos->type=goto_program_instruction_typet::ASSIGN;
      pos->source_location=loc;
      const dereference_exprt lhs(get_result_variable_array_element(type));
      const symbol_exprt rhs(get_tmp_result_expr(type));
      pos->code=code_assignt(lhs, rhs);
    }
    finalise_conditional_instr_gotos();
  }

  void add_instructions()
  {
    size_t opcode=0;
    for (const std::pair<typet, size_t> &slot : slots)
    {
      const typet &type=slot.first;
      const size_t num_instrs=get_num_instructions(type);
      assert(num_instrs);
      goto_programt::targett init;
      for (size_t i=0; i < num_instrs; ++i, ++opcode)
      {
        init=add_conditional_instr_goto(opcode, ID_notequal);
        execute_instruction(init, type, i);
      }
    }
    finalise_conditional_instr_gotos();
  }

  void add_index_increment()
  {
    pos=std::prev(body.instructions.end(), 2);
    while (goto_program_instruction_typet::DEAD == pos->type)
      pos=std::prev(pos);
    const std::string idx(meta_name(INSTR_INDEX));
    const symbol_exprt idx_expr(st.lookup(idx).symbol_expr());
    const plus_exprt rhs(idx_expr, gen_one(idx_expr.type()));
    pos=cegis_assign_local_variable(st, body, pos, func_name, INSTR_INDEX, rhs);
  }

  void add_index_goto()
  {
    pos=std::prev(body.instructions.end(), 2);
    const std::string index(meta_name(INSTR_INDEX));
    const symbol_exprt index_expr(st.lookup(index).symbol_expr());
    const std::string sz(meta_name(CEGIS_PROC_PROGRAM_SIZE_PARAM_ID));
    const symbol_exprt sz_expr(st.lookup(sz).symbol_expr());
    const binary_relation_exprt guard(index_expr, ID_lt, sz_expr);
    add_goto(guard, loop_head);
  }
};
}

void generate_processor_body(symbol_tablet &st, goto_programt &body,
    const std::string &name, const cegis_operand_datat &slots)
{
  if (!slots.empty())
  {
    body_factoryt factory(st, body, name, slots);
    factory.declare_instruction_properties();
    factory.declare_temp_vars();
    factory.init_temp_vars();
    factory.add_instructions();
    factory.assign_result_vars();
    factory.add_index_increment();
    factory.add_index_goto();
  }
  body.add_instruction(goto_program_instruction_typet::END_FUNCTION);
  // TODO: Remove single-switch-cases
  // TODO: Remove goto-next
  // TODO: Remove skips
  body.compute_loop_numbers();
  body.update();
}
