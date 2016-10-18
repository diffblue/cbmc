#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <linking/zero_initializer.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/type_helper.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>

// XXX: Debug
#include <iostream>
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
#define OPCODE_MEMBER_NAME "opcode"
#define OPERAND_ID_MEMBER_NAME_PREFIX "op_"

namespace
{
std::string get_variable_array_name(const symbol_tablet &st, const typet &type)
{
  std::string result(VARIABLE_ARRAY_PREFIX);
  return result+=type2c(type, namespacet(st));
}

void create_variable_array(symbol_tablet &st, goto_functionst &gf,
    const typet &type, const size_t size)
{
  const std::string name(get_variable_array_name(st, type));
  if (st.has_symbol(name)) return;
  const typet size_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(size, size_type));
  const mp_integer width(string2integer(id2string(type.get(ID_width))));
  const pointer_typet ref_type(type, width.to_ulong());
  const array_typet array_type(ref_type, sz_expr);
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
  if (is_primitive(type)) return NUM_PRIMITIVE_OPERANDS;
  assert(!"Class type operand generation not supported.");
  return 0;
}

size_t get_max_operands(const std::map<typet, size_t> &slots)
{
  size_t max=0;
  for (const std::pair<typet, size_t> &slot : slots)
    max=std::max(max, get_max_operands(slot.first));
  return max;
}

typet get_member_type()
{
  return unsigned_char_type();
}

symbol_typet create_instruction_type(symbol_tablet &st,
    const std::map<typet, size_t> &variable_slots_per_context_type,
    const std::string &func_name)
{
  std::string instr_type_name(func_name);
  instr_type_name+= INSTR_TYPE_SUFFIX;
  struct_typet type;
  std::string tag(TAG_PREFIX);
  tag+=instr_type_name;
  type.set_tag(tag);
  struct_union_typet::componentst &comps=type.components();
  const typet member_type(get_member_type());
  comps.push_back(struct_typet::componentt(OPCODE_MEMBER_NAME, member_type));
  const size_t max_operands=get_max_operands(variable_slots_per_context_type);
  for (size_t i=0; i < max_operands; ++i)
  {
    std::string name(OPERAND_ID_MEMBER_NAME_PREFIX);
    name+=std::to_string(i);
    struct_union_typet::componentt comp(name, member_type);
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
  mp_integer width(0);
  for (const struct_union_typet::componentt &comp : comps)
    width+=get_width(comp.type());
  const pointer_typet instr_ref_type(instruction_type, width.to_ulong());
  code_type.parameters().push_back(code_typet::parametert(instr_ref_type));
  const typet size_type(unsigned_char_type());
  code_type.parameters().push_back(code_typet::parametert(size_type));
  return code_type;
}
}

#define PROGRAM_PARAM_ID "program"
#define PROGRAM_SIZE_PARAM_ID "size"

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
  goto_programt &body=func.body;
  // TODO: Implement
  // XXX: Debug
  std::cout << "<create_cegis_processor>" << std::endl;
  gf.output(namespacet(st), std::cout);
  std::cout << "</create_cegis_processor>" << std::endl;
  // XXX: Debug
  return func_name;
}
