/*******************************************************************\

Module: Unit test for call graph generation

Author:

\*******************************************************************/

#include <iostream>

#include <testing-utils/catch.hpp>

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

static bool graph_key_matches(
  const call_grapht graph,
  const irep_idt &key,
  const std::unordered_set<irep_idt, irep_id_hash> &values)
{
  std::unordered_set<irep_idt, irep_id_hash> matching_set =
      graph.get_successors(key);
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

    goto_modelt goto_model;
    code_typet void_function_type;

    {
      code_blockt calls;
      code_function_callt call1;
      call1.function()=symbol_exprt("A", void_function_type);
      code_function_callt call2;
      call2.function()=symbol_exprt("B", void_function_type);
      calls.move_to_operands(call1);
      calls.move_to_operands(call2);

      goto_model.symbol_table.add(
        create_void_function_symbol("A", calls));
    }

    {
      code_blockt calls;
      code_function_callt call1;
      call1.function()=symbol_exprt("C", void_function_type);
      code_function_callt call2;
      call2.function()=symbol_exprt("D", void_function_type);
      calls.move_to_operands(call1);
      calls.move_to_operands(call2);

      goto_model.symbol_table.add(
        create_void_function_symbol("B", calls));
    }

    goto_model.symbol_table.add(
      create_void_function_symbol("C", code_skipt()));
    goto_model.symbol_table.add(
      create_void_function_symbol("D", code_skipt()));

    stream_message_handlert msg(std::cout);
    goto_convert(goto_model, msg);

    call_grapht call_graph_from_goto_functions(goto_model);

    WHEN("A call graph is constructed from the GOTO functions")
    {
      THEN("We expect A -> { A, B }, B -> { C, D }")
      {
        REQUIRE(call_graph_from_goto_functions.size()==4);
        REQUIRE(graph_key_matches
            (call_graph_from_goto_functions, "A", {"A", "B"}));
        REQUIRE(graph_key_matches
            (call_graph_from_goto_functions, "B", {"C", "D"}));
      }
    }

    WHEN("The call graph is inverted")
    {
      call_grapht inverse_call_graph_from_goto_functions=
        call_graph_from_goto_functions.get_inverted();
      THEN("We expect A -> { A }, B -> { A }, C -> { B }, D -> { B }")
      {
        REQUIRE(inverse_call_graph_from_goto_functions.size()==4);
        REQUIRE(graph_key_matches
            (inverse_call_graph_from_goto_functions, "A", {"A"}));
        REQUIRE(graph_key_matches
            (inverse_call_graph_from_goto_functions, "B", {"A"}));
        REQUIRE(graph_key_matches
            (inverse_call_graph_from_goto_functions, "C", {"B"}));
        REQUIRE(graph_key_matches
            (inverse_call_graph_from_goto_functions, "D", {"B"}));
      }
    }

  }

}
