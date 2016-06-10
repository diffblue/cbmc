#include <set>

#include <util/substitute.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <test_gen/java_test_source_factory.h>

namespace
{
void add_test_class_name(std::string &result, const std::string &func_name)
{
  result+="class ";
  result+=func_name;
  result+="Test {\n";
  result+="  public void test";
  result+=func_name;
  result+="() {\n";
}

void add_symbol(std::string &result, const symbolt &symbol)
{
  // TODO: Implement
}

void add_value(std::string &result, const exprt &value)
{
  // TODO: Implement
}

void add_assign_value(std::string &result, const symbolt &symbol,
    const exprt &value)
{
  add_symbol(result, symbol);
  result+='=';
  add_value(result, value);
  result+=";\n";
}

void add_global_state_assignments(std::string &result, const symbol_tablet &st,
    const inputst &inputs)
{
  for (const inputst::value_type &input : inputs)
  {
    const symbolt &symbol=st.lookup(input.first);
    if (!symbol.is_static_lifetime) continue;
    add_assign_value(result, symbol, input.second);
  }
}

void add_decl_with_init_prefix(std::string &result, const symbolt &symbol)
{
  // TODO: Implement
}

std::set<irep_idt> get_parameters(const symbolt &func)
{
  std::set<irep_idt> result;
  const code_typet &code_type=to_code_type(func.type);
  const code_typet::parameterst &params=code_type.parameters();
  for (const code_typet::parametert &param : params)
    result.insert(param.get_identifier());
  return result;
}

void add_func_call_parameters(std::string &result, const symbol_tablet &st,
    const irep_idt &func_id, const inputst &inputs)
{
  const symbolt &func=st.lookup(func_id);
  const std::set<irep_idt> params(get_parameters(func));
  for (const irep_idt &param : params)
  {
    const symbolt &symbol=st.lookup(param);
    const inputst::const_iterator value=inputs.find(param);
    assert(inputs.end() != value);
    add_decl_with_init_prefix(result, symbol);
    add_assign_value(result, symbol, value->second);
  }
}

std::string &add_func_call(std::string &result, const symbol_tablet &st,
    const irep_idt &func_id)
{
  // TODO: Implement
  return result;
}

std::string get_escaped_func_name(const symbolt &symbol)
{
  std::string result(id2string(symbol.pretty_name));
  substitute(result, ".", "_");
  substitute(result, "(", "X");
  substitute(result, ")", "Y");
  return result;
}
}

std::string generate_java_test_case_from_inputs(const symbol_tablet &st,
    const irep_idt &func_id, const inputst &inputs)
{
  const symbolt &func=st.lookup(func_id);
  const std::string func_name(get_escaped_func_name(func));
  std::string result;
  add_test_class_name(result, func_name);
  add_global_state_assignments(result, st, inputs);
  add_func_call_parameters(result, st, func_id, inputs);
  return add_func_call(result, st, func_id);
}
