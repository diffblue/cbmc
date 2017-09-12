
#include <iostream>

#include <catch.hpp>

#include <analyses/call_graph.h>

#include <util/symbol_table.h>
#include <util/std_code.h>

#include <goto-programs/goto_convert_functions.h>

static symbolt create_void_function_symbol(
  const irep_idt &name,
  const codet &code)
{
  code_typet void_function_type;
  symbolt function;
  function.name=name;
  function.type=void_function_type;
  function.mode=ID_java;
  function.value=code;
  return function;
}

static bool multimap_key_matches(
  const std::multimap<irep_idt, irep_idt> &map,
  const irep_idt &key,
  const std::set<irep_idt> &values)
{
  auto matching_values=map.equal_range(key);
  std::set<irep_idt> matching_set;
  for(auto it=matching_values.first; it!=matching_values.second; ++it)
    matching_set.insert(it->second);
  return matching_set==values;
}

SCENARIO("call_graph",
  "[core][util][call_graph]")
{

  GIVEN("Some cyclic function calls")
  {

    // Create code like:
    // void A()
    // {
    //    A();
    //    B();
    // }
    // void B()
    // {
    //   C();
    //   D();
    // }
    // void C() { }
    // void D() { }

    symbol_tablet symbol_table;
    code_typet void_function_type;

    {
      code_blockt calls;
      code_function_callt call1;
      call1.function()=symbol_exprt("A", void_function_type);
      code_function_callt call2;
      call2.function()=symbol_exprt("B", void_function_type);
      calls.move_to_operands(call1);
      calls.move_to_operands(call2);

      symbol_table.add(create_void_function_symbol("A", calls));
    }

    {
      code_blockt calls;
      code_function_callt call1;
      call1.function()=symbol_exprt("C", void_function_type);
      code_function_callt call2;
      call2.function()=symbol_exprt("D", void_function_type);
      calls.move_to_operands(call1);
      calls.move_to_operands(call2);

      symbol_table.add(create_void_function_symbol("B", calls));
    }

    symbol_table.add(create_void_function_symbol("C", code_skipt()));
    symbol_table.add(create_void_function_symbol("D", code_skipt()));

    goto_functionst goto_functions;
    stream_message_handlert msg(std::cout);
    goto_convert(symbol_table, goto_functions, msg);

    call_grapht call_graph_from_goto_functions(goto_functions);

    WHEN("A call graph is constructed from the GOTO functions")
    {
      THEN("We expect A -> { A, B }, B -> { C, D }")
      {
        const auto &check_graph=call_graph_from_goto_functions.graph;
        REQUIRE(check_graph.size()==4);
        REQUIRE(multimap_key_matches(check_graph, "A", {"A", "B"}));
        REQUIRE(multimap_key_matches(check_graph, "B", {"C", "D"}));
      }
    }

    WHEN("The call graph is inverted")
    {
      call_grapht inverse_call_graph_from_goto_functions=
        call_graph_from_goto_functions.get_inverted();
      THEN("We expect A -> { A }, B -> { A }, C -> { B }, D -> { B }")
      {
        const auto &check_graph=inverse_call_graph_from_goto_functions.graph;
        REQUIRE(check_graph.size()==4);
        REQUIRE(multimap_key_matches(check_graph, "A", {"A"}));
        REQUIRE(multimap_key_matches(check_graph, "B", {"A"}));
        REQUIRE(multimap_key_matches(check_graph, "C", {"B"}));
        REQUIRE(multimap_key_matches(check_graph, "D", {"B"}));
      }
    }

  }

}
