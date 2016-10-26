#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <linking/zero_initializer.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>

// XXX: Debug
#include <iostream>

#include <cegis/refactor/instructionset/execute_cegis_program.h>
// XXX: Debug

namespace
{
class type_collectort: public const_expr_visitort
{
public:
  std::set<typet> types;

  virtual ~type_collectort()=default;

  virtual void operator()(const exprt &expr)
  {
    types.insert(expr.type());
  }
};
}

std::set<typet> collect_context_types(const goto_ranget &range)
{
  type_collectort collector;
  for (goto_programt::const_targett it(range.first); it != range.second; ++it)
    it->code.visit(collector);
  return collector.types;
}

std::map<typet, size_t> slots_per_type(const symbol_tablet &st,
    const std::set<irep_idt> &state_vars)
{
  const namespacet ns(st);
  std::map<typet, size_t> result;
  for (const irep_idt &state_var : state_vars)
    ++result[ns.follow(st.lookup(state_var).type)];
  return result;
}

#define MAX_PROCESSORS 128u
#define CEGIS_PROCESSOR_FUNCTION_PREFIX CEGIS_PREFIX "processor_"
#define INSTR_TYPE_SUFFIX "_instructiont"
#define VARIABLE_ARRAY_PREFIX CEGIS_PREFIX "variable_array_"
#define NUM_PRIMITIVE_OPERANDS 2u
#define NUM_PRIMITIVE_OPCODES 4u
#define OPCODE_MEMBER_NAME "opcode"
#define OPERAND_ID_MEMBER_NAME_PREFIX "op_"
#define OPERAND_TMP_RESULT_PREFIX "result_op_"
#define INSTR_INDEX "i"
#define PROGRAM_PARAM_ID "program"
#define PROGRAM_SIZE_PARAM_ID "size"

namespace
{
std::string get_variable_array_name(const symbol_tablet &st, const typet &type)
{
  std::string result(VARIABLE_ARRAY_PREFIX);
  return result+=type2c(type, namespacet(st));
}

symbol_exprt get_variable_array_symbol(const symbol_tablet &st,
    const typet &type)
{
  return st.lookup(get_variable_array_name(st, type)).symbol_expr();
}

void create_variable_array(symbol_tablet &st, goto_functionst &gf,
    const typet &type, const size_t size)
{
  const std::string name(get_variable_array_name(st, type));
  if (st.has_symbol(name)) return;
  const typet size_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(size, size_type));
  const array_typet array_type(pointer_typet(type), sz_expr);
  symbolt new_symbol;
  new_symbol.name=name;
  new_symbol.type=array_type;
  new_symbol.base_name=name;
  new_symbol.pretty_name=name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  new_symbol.is_static_lifetime=true;
  new_symbol.is_lvalue=true;
  assert(!st.add(new_symbol));
  goto_programt &body=get_body(gf, CPROVER_INIT);
  goto_programt::targett pos=body.instructions.begin();
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=new_symbol.location;
  const symbol_exprt lhs(st.lookup(name).symbol_expr());
  const namespacet ns(st);
  null_message_handlert msg;
  const exprt rhs(zero_initializer(array_type, new_symbol.location, ns, msg));
  pos->code=code_assignt(lhs, rhs);
  body.update();
}

std::string get_next_processor_name(const symbol_tablet &st)
{
  std::string name(CEGIS_PROCESSOR_FUNCTION_PREFIX);
  for (size_t index=0; index < MAX_PROCESSORS; ++index)
  {
    name+=std::to_string(index);
    if (!st.has_symbol(name)) return name;
    else name= CEGIS_PROCESSOR_FUNCTION_PREFIX;
  }
  assert(!"Exceeded maximum number of CEGIS processors.");
  return "";
}

bool is_primitive(const typet &type)
{
  const irep_idt &id=type.id();
  return ID_c_bool == id || ID_floatbv == id || ID_unsignedbv == id
      || ID_signedbv == id;
}

size_t get_max_operands(const typet &type)
{
  if (!is_primitive(type))
  assert(!"Class type operand generation not supported.");
  return NUM_PRIMITIVE_OPERANDS;
}

size_t get_num_instructions(const typet &type)
{
  if (!is_primitive(type))
  assert(!"Class type operand generation not supported.");
  return NUM_PRIMITIVE_OPCODES;
}

size_t get_max_operands(const std::map<typet, size_t> &slots)
{
  size_t max=0;
  for (const std::pair<typet, size_t> &slot : slots)
    max=std::max(max, get_max_operands(slot.first));
  return max;
}

std::string get_op(const size_t op)
{
  std::string name(OPERAND_ID_MEMBER_NAME_PREFIX);
  return name+=std::to_string(op);
}

symbol_typet create_instruction_type(symbol_tablet &st,
    const std::map<typet, size_t> &variable_slots_per_context_type,
    const std::string &func_name)
{
  std::string instr_type_name(func_name);
  instr_type_name+= INSTR_TYPE_SUFFIX;
  if (st.has_symbol(instr_type_name)) return symbol_typet(instr_type_name);
  struct_typet type;
  std::string tag(TAG_PREFIX);
  tag+=instr_type_name;
  type.set_tag(tag);
  struct_union_typet::componentst &comps=type.components();
  const typet opcode_type(cegis_opcode_type());
  comps.push_back(struct_typet::componentt(OPCODE_MEMBER_NAME, opcode_type));
  const size_t max_operands=get_max_operands(variable_slots_per_context_type);
  for (size_t i=0; i < max_operands; ++i)
  {
    struct_union_typet::componentt comp(get_op(i), cegis_operand_type());
    comps.push_back(comp);
  }
  symbolt new_symbol;
  new_symbol.name=instr_type_name;
  new_symbol.type=type;
  new_symbol.base_name=instr_type_name;
  new_symbol.pretty_name=instr_type_name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  new_symbol.is_type=true;
  assert(!st.add(new_symbol));
  return symbol_typet(instr_type_name);
}

const mp_integer get_width(const typet &type)
{
  const irep_idt &id_width=type.get(ID_width);
  assert(!id_width.empty());
  return string2integer(id2string(id_width));
}

code_typet create_func_type(const symbol_tablet &st,
    const symbol_typet &instruction_type)
{
  code_typet code_type;
  code_type.return_type()=empty_typet();
  const typet &followed_type=namespacet(st).follow(instruction_type);
  const struct_union_typet &struct_type=to_struct_union_type(followed_type);
  const struct_union_typet::componentst &comps=struct_type.components();
  const pointer_typet instr_ref_type(instruction_type);
  code_type.parameters().push_back(code_typet::parametert(instr_ref_type));
  const typet size_type(unsigned_char_type());
  code_type.parameters().push_back(code_typet::parametert(size_type));
  return code_type;
}

void add_param(symbol_tablet &st, const std::string &func,
    const char * const name, const typet &type)
{
  symbolt prog_param_symbol;
  prog_param_symbol.name=get_local_meta_name(func, name);
  prog_param_symbol.type=type;
  prog_param_symbol.base_name=name;
  prog_param_symbol.pretty_name=name;
  prog_param_symbol.location=default_cegis_source_location();
  prog_param_symbol.mode=ID_C;
  prog_param_symbol.module=CEGIS_MODULE;
  prog_param_symbol.is_lvalue=true;
  prog_param_symbol.is_thread_local=true;
  prog_param_symbol.is_file_local=true;
  prog_param_symbol.is_parameter=true;
  prog_param_symbol.is_state_var=true;
  assert(!st.add(prog_param_symbol));
}

void add_to_symbol_table(symbol_tablet &st, const std::string &name,
    const goto_functionst::function_mapt::mapped_type &func)
{
  if (st.has_symbol(name)) return;
  symbolt new_symbol;
  new_symbol.name=name;
  new_symbol.type=func.type;
  new_symbol.base_name=name;
  new_symbol.pretty_name=name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  assert(!st.add(new_symbol));
  const code_typet::parameterst &params=func.type.parameters();
  assert(2 == params.size());
  add_param(st, name, PROGRAM_PARAM_ID, params.front().type());
  add_param(st, name, PROGRAM_SIZE_PARAM_ID, params.back().type());
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
  const std::map<typet, size_t> &slots;
  const goto_programt::targett end;
  goto_programt::targett dummy;
  goto_programt::targett loop_head;
  goto_programt::targett last_case;
  goto_programt::targett switch_end;
  goto_programt::targett pos;

  goto_programt::targett dead(const std::string &name)
  {
    goto_programt::targett pos=body.insert_after(this->pos);
    pos->type=goto_program_instruction_typet::DEAD;
    pos->source_location=default_cegis_source_location();
    const std::string symbol_name(get_local_meta_name(func_name, name));
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
    const std::string prog(get_local_meta_name(func_name, PROGRAM_PARAM_ID));
    const symbol_exprt prog_expr(st.lookup(prog).symbol_expr());
    const std::string index(get_local_meta_name(func_name, INSTR_INDEX));
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
    const std::string name(get_local_meta_name(func_name, OPCODE_MEMBER_NAME));
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
    const std::string name(get_local_meta_name(func_name, base_name));
    return st.lookup(name).symbol_expr();
  }

  symbol_exprt get_tmp_result_expr(const typet &type)
  {
    const std::string base_name(get_tmp_result_op(st, type));
    const std::string name(get_local_meta_name(func_name, base_name));
    return st.lookup(name).symbol_expr();
  }

  dereference_exprt get_variable_array_element(const typet &type,
      const std::string index_var_base_name)
  {
    const std::string name(get_local_meta_name(func_name, index_var_base_name));
    const symbol_exprt index(st.lookup(name).symbol_expr());
    const std::string array_name(get_variable_array_name(st, type));
    const symbol_exprt array(st.lookup(array_name).symbol_expr());
    return dereference_exprt(index_exprt(array, index));
  }

  dereference_exprt get_op_variable_array_element(const typet &type,
      const size_t op_id)
  {
    return get_variable_array_element(type, get_op(op_id));
  }

  dereference_exprt get_result_variable_array_element(const typet &type)
  {
    const std::string base_name(get_tmp_result_op(st, type));
    return get_variable_array_element(type, base_name);
  }
public:
  body_factoryt(symbol_tablet &st, goto_programt &body, const std::string &name,
      const std::map<typet, size_t> &slots) :
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
    decl_instr_member(OPCODE_MEMBER_NAME);
    loop_head=std::prev(pos);
    const size_t global_max_operands=get_max_operands(slots);
    for (size_t i=0; i < global_max_operands; ++i)
      decl_instr_member(get_op(i));
  }

  void declare_temp_vars()
  {
    for (const std::pair<typet, size_t> &slot : slots)
    {
      const typet &type=slot.first;
      const size_t max_operands=get_max_operands(type);
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
      const size_t max_operands=get_max_operands(type);
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
      const size_t max_operands=get_max_operands(type);
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
    const std::string idx(get_local_meta_name(func_name, INSTR_INDEX));
    const symbol_exprt idx_expr(st.lookup(idx).symbol_expr());
    const plus_exprt rhs(idx_expr, gen_one(idx_expr.type()));
    pos=cegis_assign_local_variable(st, body, pos, func_name, INSTR_INDEX, rhs);
  }

  void add_index_goto()
  {
    pos=std::prev(body.instructions.end(), 2);
    const std::string index(get_local_meta_name(func_name, INSTR_INDEX));
    const symbol_exprt index_expr(st.lookup(index).symbol_expr());
    const std::string sz(get_local_meta_name(func_name, PROGRAM_SIZE_PARAM_ID));
    const symbol_exprt sz_expr(st.lookup(sz).symbol_expr());
    const binary_relation_exprt guard(index_expr, ID_lt, sz_expr);
    add_goto(guard, loop_head);
  }
};

void generate_processor_body(symbol_tablet &st, goto_programt &body,
    const std::string &name, const std::map<typet, size_t> &slots)
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
}

std::string create_cegis_processor(symbol_tablet &st, goto_functionst &gf,
    const std::map<typet, size_t> &slots)
{
  for (const std::pair<typet, size_t> &var_slot : slots)
    create_variable_array(st, gf, var_slot.first, var_slot.second);
  const std::string func_name(get_next_processor_name(st));
  const symbol_typet instr_type(create_instruction_type(st, slots, func_name));
  goto_functionst::function_mapt::mapped_type &func=gf.function_map[func_name];
  func.parameter_identifiers.push_back(PROGRAM_PARAM_ID);
  func.parameter_identifiers.push_back(PROGRAM_SIZE_PARAM_ID);
  func.type=create_func_type(st, instr_type);
  add_to_symbol_table(st, func_name, func);
  goto_programt &body=func.body;
  generate_processor_body(st, body, func_name, slots);
  // TODO: Implement
  // XXX: Debug
  goto_programt &entry_body=get_entry_body(gf);
  std::string prog(func_name);
  prog+="_prog";
  declare_cegis_program(st, gf, func_name, prog, 3);
  call_processor(st, entry_body, std::prev(entry_body.instructions.end(), 2),
      func_name, prog);
  try
  {
    std::cout << "<create_cegis_processor>" << std::endl;
    st.show(std::cout);
    gf.output(namespacet(st), std::cout);
    std::cout << "</create_cegis_processor>" << std::endl;
  } catch (const std::string &ex)
  {
    std::cout << "<ex>" << ex << "</ex>" << std::endl;
    throw;
  }
  // XXX: Debug
  return func_name;
}
