#include <cegis/instrument/literals.h>

#include <cegis/refactor/instructionset/create_cegis_processor.h>

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

#define CEGIS_PROCESSOR_FUNCTION_PREFIX CEGIS_PREFIX "processor_"

std::string get_next_processor_name(const symbol_tablet &st)
{
  size_t index=0;
  std::string name(CEGIS_PROCESSOR_FUNCTION_PREFIX);
  while (st.has_symbol(name + std::to_string(index)))
    ++index;
  return name+=std::to_string(index);
}

std::string create_cegis_processor(symbol_tablet &st, goto_functionst &gf,
    const std::map<typet, size_t> &variable_slots_per_context_type)
{
  std::string processor_name(CEGIS_PROCESSOR_FUNCTION_PREFIX);
  // TODO: Implement
  assert(false);
}
