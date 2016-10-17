#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <linking/zero_initializer.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/cegis-util/program_helper.h>
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
#define VARIABLE_ARRAY_PREFIX CEGIS_PREFIX "variable_array_"

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
}

std::string create_cegis_processor(symbol_tablet &st, goto_functionst &gf,
    const std::map<typet, size_t> &variable_slots_per_context_type)
{
  for (const std::pair<typet, size_t> &slot_with_type : variable_slots_per_context_type)
    create_variable_array(st, gf, slot_with_type.first, slot_with_type.second);
  const std::string processor_name(get_next_processor_name(st));
  // TODO: Implement
  // XXX: Debug
  std::cout << "<create_cegis_processor>" << std::endl;
  gf.output(namespacet(st), std::cout);
  std::cout << "</create_cegis_processor>" << std::endl;
  // XXX: Debug
  return processor_name;
}
