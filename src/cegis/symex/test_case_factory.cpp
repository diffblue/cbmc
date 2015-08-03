/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <goto-programs/goto_functions.h>

#include <cegis/options/cegis_options.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/test_case_factory.h>

test_case_factoryt::test_case_factoryt(symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory,
    const exprt &synthesis_property) :
    st(st), gf(gf), options(options), lfactory(lfactory), synthesis_property(
        synthesis_property), counterexample_count(0)
{
}

test_case_factoryt::~test_case_factoryt()
{
}

namespace {
class add_assignmentt
{
  typedef test_case_factoryt::counterexamplet::value_type assignmentt;
  const symbol_tablet &symbol_table;
  goto_functionst &gf;
  const cegis_optionst &options;
  source_location_factoryt &lfactory;
public:
  add_assignmentt(const symbol_tablet &symbol_table, goto_functionst &gf,
      const cegis_optionst &options, source_location_factoryt &lfactory) :
      symbol_table(symbol_table), gf(gf), options(options), lfactory(lfactory)
  {
  }

  void operator()(const assignmentt &assignment) const
  {
    const irep_idt &symbol_name(assignment.first);
    assert(symbol_table.has_symbol(symbol_name));
    const symbol_exprt lhs=symbol_table.lookup(symbol_name).symbol_expr();
    const std::string entry_function_name=options.entry_function_name();
    goto_programt &body=get_program_body(gf, entry_function_name);
    const goto_programt::targett assign=body.add_instruction(ASSIGN);
    assign->code=code_assignt(lhs, assignment.second);
    assign->source_location=lfactory(entry_function_name);
  }
};

void assign_test_input_values(const symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory,
    const test_case_factoryt::counterexamplet &ce)
{
  const add_assignmentt add_assignment(st, gf, options, lfactory);
  std::for_each(ce.begin(), ce.end(), add_assignment);
}

void run_synthesis_root(const symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory)
{
  const std::string synthesis_root(options.root_function_name());
  assert(st.has_symbol(synthesis_root));
  const symbol_exprt fn=st.lookup(synthesis_root).symbol_expr();
  const std::string synthesis_entry(options.entry_function_name());
  goto_programt &body=get_program_body(gf, synthesis_entry);
  const goto_programt::targett call=body.add_instruction(FUNCTION_CALL);
  code_function_callt function_call;
  function_call.function()=fn;
  call->code=function_call;
  call->source_location=lfactory(synthesis_entry);
}

std::string property_var_name(const size_t counterexample_count)
{
  std::string result("__CPROVER_synthesis_property_");
  return result+=integer2string(counterexample_count);
}

void store_assertion_result(symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory,
    const exprt &property, size_t &counterexample_count)
{
  const std::string synthesis_entry(options.entry_function_name());
  goto_programt &body=get_program_body(gf, synthesis_entry);
  goto_program_adaptert adapter(st, body);
  const std::string property_var(property_var_name(counterexample_count));
  ++counterexample_count;
  const bool_typet ptype;
  const source_locationt decl_loc(lfactory(synthesis_entry));
  const code_declt &decl=adapter.append_decl(property_var, ptype, decl_loc);
  const exprt &lhs=decl.symbol();
  const goto_programt::targett assign=body.add_instruction(ASSIGN);
  assign->code=code_assignt(lhs, property);
  assign->source_location=lfactory(synthesis_entry);
}
}

void test_case_factoryt::operator ()(const counterexamplet &ce)
{
  assign_test_input_values(st, gf, options, lfactory, ce);
  run_synthesis_root(st, gf, options, lfactory);
  store_assertion_result(st, gf, options, lfactory, synthesis_property,
      counterexample_count);
}

void add_result_verification_assertion(goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &lfactory,
    const exprt &safety_property, const size_t counterexample_count)
{
  exprt::operandst operands;
  const bool_typet ptype;
  for (size_t i=0; i <= counterexample_count; ++i)
  {
    const symbol_exprt assertion_result(property_var_name(i), ptype);
    const unary_predicate_exprt neg(ID_not, assertion_result);
    operands.push_back(neg);
  }
  const std::string entry_name(options.entry_function_name());
  goto_programt &body=get_program_body(gf, entry_name);
  const goto_programt::targett summary_assert=body.add_instruction(ASSERT);
  summary_assert->guard=disjunction(operands);
  summary_assert->source_location=lfactory(entry_name);
}

size_t test_case_factoryt::get_counterexample_count() const
{
  return counterexample_count - 1;
}
