/*******************************************************************\

Module: Unit test for graph class functions

Author:

\*******************************************************************/

#include <iostream>

#include <testing-utils/call_graph_test_utils.h>
#include <testing-utils/use_catch.h>

#include <analyses/call_graph_helpers.h>

#include <util/symbol_table.h>

#include <goto-programs/goto_convert_functions.h>

SCENARIO("graph", "[core][util][graph]")
{
  GIVEN("Some cyclic function calls")
  {
    // Create code like:
    // void A()
    // {
    //    A();
    //    B();
    //    B();
    // }
    // void B()
    // {
    //   C();
    //   D();
    // }
    // void C() { }
    // void D() { }
    // void E()
    // {
    //    F();
    //    G();
    // }
    // void F() { }
    // void G() { }

    goto_modelt goto_model;
    code_typet void_function_type({}, empty_typet());

    {
      code_blockt calls(
        {code_function_callt(symbol_exprt("A", void_function_type)),
         code_function_callt(symbol_exprt("B", void_function_type))});

      goto_model.symbol_table.add(create_void_function_symbol("A", calls));
    }

    {
      code_blockt calls(
        {code_function_callt(symbol_exprt("C", void_function_type)),
         code_function_callt(symbol_exprt("D", void_function_type))});

      goto_model.symbol_table.add(create_void_function_symbol("B", calls));
    }

    {
      code_blockt calls(
        {code_function_callt(symbol_exprt("F", void_function_type)),
         code_function_callt(symbol_exprt("G", void_function_type))});

      goto_model.symbol_table.add(create_void_function_symbol("E", calls));
    }

    goto_model.symbol_table.add(create_void_function_symbol("C", code_skipt()));
    goto_model.symbol_table.add(create_void_function_symbol("D", code_skipt()));
    goto_model.symbol_table.add(create_void_function_symbol("F", code_skipt()));
    goto_model.symbol_table.add(create_void_function_symbol("G", code_skipt()));

    stream_message_handlert msg(std::cout);
    goto_convert(goto_model, msg);

    call_grapht call_graph_from_goto_functions(goto_model);

    WHEN("A call graph is constructed from the GOTO functions")
    {
      THEN("We expect A -> { A, B, B }, B -> { C, D }, E -> { F, G }")
      {
        const auto &check_graph = call_graph_from_goto_functions.edges;
        REQUIRE(check_graph.size() == 6);
        REQUIRE(multimap_key_matches(check_graph, "A", {"A", "B", "B"}));
        REQUIRE(multimap_key_matches(check_graph, "B", {"C", "D"}));
        REQUIRE(multimap_key_matches(check_graph, "E", {"F", "G"}));
      }
    }

    WHEN("The call graph is exported as a grapht")
    {
      call_grapht::directed_grapht exported =
        call_graph_from_goto_functions.get_directed_graph();

      typedef call_grapht::directed_grapht::node_indext node_indext;
      std::map<irep_idt, node_indext> nodes_by_name;
      for(node_indext i = 0; i < exported.size(); ++i)
        nodes_by_name[exported[i].function] = i;

      THEN("We expect 7 nodes")
      {
        REQUIRE(exported.size() == 7);
      }

      THEN("We expect edges A -> { A, B }, B -> { C, D }, E -> { F, G }")
      {
        // Note that means the extra A -> B edge has gone away (the grapht
        // structure can't represent the parallel edge)
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["A"]));
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["B"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["C"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["D"]));
        REQUIRE(exported.has_edge(nodes_by_name["E"], nodes_by_name["F"]));
        REQUIRE(exported.has_edge(nodes_by_name["E"], nodes_by_name["G"]));
      }

      THEN("We expect G to have predecessors {E}")
      {
        std::set<irep_idt> predecessors = get_callers(exported, "G");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("E"));
      }

      THEN("We expect F to have predecessors {E}")
      {
        std::set<irep_idt> predecessors = get_callers(exported, "F");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("E"));
      }

      THEN("We expect {E} to be able to reach E")
      {
        std::set<irep_idt> predecessors = get_reaching_functions(exported, "E");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("E"));
      }
    }

    WHEN("functions unreachable from A in the grapht are disconnected")
    {
      call_grapht::directed_grapht exported =
        call_graph_from_goto_functions.get_directed_graph();

      typedef call_grapht::directed_grapht::node_indext node_indext;
      std::map<irep_idt, node_indext> nodes_by_name;
      for(node_indext i = 0; i < exported.size(); ++i)
        nodes_by_name[exported[i].function] = i;

      exported.disconnect_unreachable(nodes_by_name["A"]);

      THEN("We expect edges A -> { A, B }, B -> { C, D }")
      {
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["A"]));
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["B"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["C"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["D"]));
      }

      THEN("We expect {E} to be able to reach E")
      {
        std::set<irep_idt> predecessors = get_reaching_functions(exported, "E");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("E"));
      }

      THEN("We expect {F} to be able to reach F")
      {
        std::set<irep_idt> predecessors = get_reaching_functions(exported, "F");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("F"));
      }

      THEN("We expect {G} to be able to reach G")
      {
        std::set<irep_idt> predecessors = get_reaching_functions(exported, "G");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("G"));
      }
    }
  }
}
