#include <algorithm>
#include <set>

#include <util/substitute.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include <java_bytecode/expr2java.h>

#include <test_gen/java_test_source_factory.h>

#define INDENT_SPACES "  "
#define JAVA_NS_PREFIX_LEN 6u

namespace
{
std::string &indent(std::string &result, const size_t num_indent=1u)
{
  for (size_t i=0u; i < num_indent; ++i)
    result+=INDENT_SPACES;
  return result;
}

void add_test_class_name(std::string &result, const std::string &func_name)
{
  result+="class ";
  result+=func_name;
  result+="Test {\n";
  indent(result)+="public void test";
  result+=func_name;
  result+="() {\n";
}

void add_symbol(std::string &result, const symbolt &s)
{
  // XXX: Should be expr2java(...) once functional.
  const irep_idt &n=s.pretty_name.empty() ? s.base_name : s.pretty_name;
  result+=id2string(n);
}

void add_qualified_class_name(std::string &result, const namespacet &ns,
    const typet &type)
{
  if (ID_symbol == type.id())
  {
    const std::string &id=id2string(to_symbol_type(type).get_identifier());
    assert(id.size() >= JAVA_NS_PREFIX_LEN);
    result+=id.substr(JAVA_NS_PREFIX_LEN);
  } else result+=id2string(to_struct_type(type).get_tag());
}

void add_decl_with_init_prefix(std::string &result, const symbol_tablet &st,
    const symbolt &symbol)
{
  const namespacet ns(st);
  if (ID_pointer != symbol.type.id()) result+=type2java(symbol.type, ns);
  else add_qualified_class_name(result, ns, symbol.type.subtype());
  result+=' ';
}

void add_value(std::string &result, const symbol_tablet &st,
    const struct_exprt &value, const std::string &this_name);

void add_value(std::string &result, const symbol_tablet &st, const exprt &value,
    const std::string var_name="")
{
  const namespacet ns(st);
  const irep_idt &id=value.id();
  if (ID_address_of == id) add_value(result, st,
      to_address_of_expr(value).object());
  else if (ID_struct == id) add_value(result, st, to_struct_expr(value),
      var_name);
  else result+=expr2java(value, ns);
}

class member_factoryt
{
  std::string &result;
  const symbol_tablet &st;
  const std::string &this_name;
  const struct_typet::componentst &comps;
  size_t comp_index;

public:
  member_factoryt(std::string &result, const symbol_tablet &st,
      const std::string &this_name, const typet &type) :
      result(result), st(st), this_name(this_name), comps(
          to_struct_type(type).components()), comp_index(0u)
  {
  }

  void operator()(const exprt &value)
  {
    assert(comp_index < comps.size());
    if (ID_struct == value.id())
    {
      member_factoryt mem_fac(result, st, this_name, value.type());
      const struct_exprt::operandst &ops=value.operands();
      std::for_each(ops.begin(), ops.end(), mem_fac);
      if (comp_index < comps.size() - 1) result+=";\n";
    } else
    {
      const struct_typet::componentt &comp=comps[comp_index];
      if (ID_symbol != comp.type().id())
      {
        indent(result, 2u)+="Reflector.setInstanceField(";
        result+=this_name;
        result+=",\"";
        result+=id2string(comp.get_pretty_name());
        result+="\",";
        add_value(result, st, value);
        result+=")";
        if (comp_index < comps.size() - 1) result+=";\n";
      }
    }
    ++comp_index;
  }
};

void add_value(std::string &result, const symbol_tablet &st,
    const struct_exprt &value, const std::string &this_name)
{
  const namespacet ns(st);
  result+='(';
  const typet &type=value.type();
  add_qualified_class_name(result, ns, type);
  result+=") Reflector.forceInstance(\"";
  add_qualified_class_name(result, ns, type);
  result+="\");\n";
  member_factoryt mem_fac(result, st, this_name, type);
  const struct_exprt::operandst &ops=value.operands();
  std::for_each(ops.begin(), ops.end(), mem_fac);
}

void add_assign_value(std::string &result, const symbol_tablet &st,
    const symbolt &symbol, const exprt &value)
{
  std::string symbol_name;
  add_symbol(symbol_name, symbol);
  result+=symbol_name;
  result+='=';
  add_value(result, st, value, symbol_name);
  result+=";\n";
}

void add_global_state_assignments(std::string &result, const symbol_tablet &st,
    inputst &inputs)
{
  for (inputst::value_type &input : inputs)
  {
    const symbolt &symbol=st.lookup(input.first);
    if (!symbol.is_static_lifetime) continue;
    add_assign_value(indent(result, 2u), st, symbol, input.second);
  }
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
    const irep_idt &func_id, inputst &inputs)
{
  const symbolt &func=st.lookup(func_id);
  const std::set<irep_idt> params(get_parameters(func));
  for (const irep_idt &param : params)
  {
    const symbolt &symbol=st.lookup(param);
    const inputst::iterator value=inputs.find(param);
    assert(inputs.end() != value);
    add_decl_with_init_prefix(indent(result, 2u), st, symbol);
    add_assign_value(result, st, symbol, value->second);
  }
}

std::string &add_func_call(std::string &result, const symbol_tablet &st,
    const irep_idt &func_id)
{
  // XXX: Should be expr2java(...) once functional.
  const symbolt &s=st.lookup(func_id);
  const std::string func_name_with_brackets(id2string(s.pretty_name));
  const size_t sz=func_name_with_brackets.size();
  assert(sz >= 2u);
  indent(result, 2u)+=func_name_with_brackets.substr(0, sz - 2);
  result+='(';
  const std::set<irep_idt> params(get_parameters(s));
  for (const irep_idt &param : params)
  {
    add_symbol(result, st.lookup(param));
    result+=',';
  }
  *result.rbegin()=')';
  result+=";\n";
  indent(result)+="}\n";
  return result+="}\n";
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
    const irep_idt &func_id, inputst inputs)
{
  const symbolt &func=st.lookup(func_id);
  const std::string func_name(get_escaped_func_name(func));
  std::string result;
  add_test_class_name(result, func_name);
  add_global_state_assignments(result, st, inputs);
  add_func_call_parameters(result, st, func_id, inputs);
  return add_func_call(result, st, func_id);
}
