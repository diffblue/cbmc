/*******************************************************************\

Module: Unit test for call graph generation

Author:

\*******************************************************************/

#include <iostream>

#include <testing-utils/call_graph_test_utils.h>
#include <testing-utils/catch.hpp>

#include <analyses/call_graph.h>
#include <analyses/call_graph_helpers.h>

#include <util/symbol_table.h>

#include <goto-programs/goto_convert_functions.h>



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
    //    B();
    // }
    // void B()
    // {
    //   C();
    //   D();
    // }
    // void C() { }
    // void D() { }
    // void E() { }

    goto_modelt goto_model;
    code_typet void_function_type({}, empty_typet());

    {
      code_blockt calls(
        {code_function_callt(symbol_exprt("A", void_function_type)),
         code_function_callt(symbol_exprt("B", void_function_type)),
         code_function_callt(symbol_exprt("B", void_function_type))});

      goto_model.symbol_table.add(
        create_void_function_symbol("A", calls));
    }

    {
      code_blockt calls(
        {code_function_callt(symbol_exprt("C", void_function_type)),
         code_function_callt(symbol_exprt("D", void_function_type))});

      goto_model.symbol_table.add(
        create_void_function_symbol("B", calls));
    }

    goto_model.symbol_table.add(
      create_void_function_symbol("C", code_skipt()));
    goto_model.symbol_table.add(
      create_void_function_symbol("D", code_skipt()));
    goto_model.symbol_table.add(
      create_void_function_symbol("E", code_skipt()));

    stream_message_handlert msg(std::cout);
    goto_convert(goto_model, msg);

    call_grapht call_graph_from_goto_functions(goto_model);

    WHEN("A call graph is constructed from the GOTO functions")
    {
      THEN("We expect A -> { A, B, B }, B -> { C, D }")
      {
        const auto &check_graph=call_graph_from_goto_functions.edges;
        REQUIRE(check_graph.size()==5);
        REQUIRE(multimap_key_matches(check_graph, "A", {"A", "B", "B"}));
        REQUIRE(multimap_key_matches(check_graph, "B", {"C", "D"}));
      }
      THEN("No callsite data should be collected")
      {
        REQUIRE(call_graph_from_goto_functions.callsites.empty());
      }
    }

    WHEN("The call graph is inverted")
    {
      call_grapht inverse_call_graph_from_goto_functions=
        call_graph_from_goto_functions.get_inverted();
      THEN("We expect A -> { A }, B -> { A, A }, C -> { B }, D -> { B }")
      {
        const auto &check_graph=inverse_call_graph_from_goto_functions.edges;
        REQUIRE(check_graph.size()==5);
        REQUIRE(multimap_key_matches(check_graph, "A", {"A"}));
        REQUIRE(multimap_key_matches(check_graph, "B", {"A", "A"}));
        REQUIRE(multimap_key_matches(check_graph, "C", {"B"}));
        REQUIRE(multimap_key_matches(check_graph, "D", {"B"}));
      }
    }

    WHEN("A call graph is constructed with call-site tracking")
    {
      call_grapht call_graph_from_goto_functions_tracking(goto_model, true);
      THEN("We expect two callsites for the A -> B edge, one for all others")
      {
        const auto &check_callsites =
          call_graph_from_goto_functions_tracking.callsites;
        for(const auto &edge : call_graph_from_goto_functions_tracking.edges)
        {
          if(edge==call_grapht::edgest::value_type("A", "B"))
            REQUIRE(check_callsites.at(edge).size()==2);
          else
            REQUIRE(check_callsites.at(edge).size()==1);
        }
      }
      WHEN("Such a graph is inverted")
      {
        call_grapht inverted =
          call_graph_from_goto_functions_tracking.get_inverted();
        THEN("The callsite data should be discarded")
        {
          REQUIRE(inverted.callsites.empty());
        }
      }
    }

    WHEN("A call graph is constructed from a root and callsite tracking is on")
    {
      call_grapht call_graph_with_specific_root =
        call_grapht::create_from_root_function(goto_model, "B", true);

      THEN("The graph should contain nodes for only B, C and D")
      {
        call_grapht::nodest correct_value {"B", "C", "D"};
        REQUIRE(call_graph_with_specific_root.nodes == correct_value);
      }
      THEN("Only B -> C and B -> D edges should exist, each with one callsite")
      {
        const auto &check_callsites=call_graph_with_specific_root.callsites;
        call_grapht::edgest correct_value { {"B", "C"}, {"B", "D"} };
        REQUIRE(call_graph_with_specific_root.edges == correct_value);
        for(const auto &edge : call_graph_with_specific_root.edges)
        {
          REQUIRE(check_callsites.at(edge).size()==1);
        }
      }
    }

    WHEN("A call-graph is constructed rooted at B")
    {
      call_grapht call_graph_from_b =
        call_grapht::create_from_root_function(goto_model, "B", false);
      THEN("We expect only B -> C and B -> D in the resulting graph")
      {
        const auto &check_graph=call_graph_from_b.edges;
        REQUIRE(check_graph.size()==2);
        REQUIRE(multimap_key_matches(check_graph, "B", {"C", "D"}));
      }
    }

    WHEN("The call graph is exported as a grapht")
    {
      call_grapht::directed_grapht exported=
        call_graph_from_goto_functions.get_directed_graph();

      typedef call_grapht::directed_grapht::node_indext node_indext;
      std::map<irep_idt, node_indext> nodes_by_name;
      for(node_indext i=0; i<exported.size(); ++i)
        nodes_by_name[exported[i].function]=i;

      THEN("We expect 5 nodes")
      {
        REQUIRE(exported.size() == 5);
      }

      THEN("We expect edges A -> { A, B }, B -> { C, D }")
      {
        // Note that means the extra A -> B edge has gone away (the grapht
        // structure can't represent the parallel edge)
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["A"]));
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["B"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["C"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["D"]));
      }

      THEN("We expect {A,B} to be reachable from {A} in 1 step")
      {
        irep_idt function_name = "A";
        std::size_t depth = 1;
        std::set<irep_idt> reachable = get_functions_reachable_within_n_steps(
          exported, function_name, depth);
        REQUIRE(reachable.size() == 2);
        REQUIRE(reachable.count("A"));
        REQUIRE(reachable.count("B"));
      }
      THEN("We expect {A,B,C,D} to be reachable from {A} in 2 and 3 steps")
      {
        irep_idt function_name = "A";
        std::size_t depth = 2;
        std::set<irep_idt> reachable = get_functions_reachable_within_n_steps(
          exported, function_name, depth);
        REQUIRE(reachable.size() == 4);
        REQUIRE(reachable.count("A"));
        REQUIRE(reachable.count("B"));
        REQUIRE(reachable.count("C"));
        REQUIRE(reachable.count("D"));

        depth = 3;
        reachable = get_functions_reachable_within_n_steps(
          exported, function_name, depth);
        REQUIRE(reachable.size() == 4);
        REQUIRE(reachable.count("A"));
        REQUIRE(reachable.count("B"));
        REQUIRE(reachable.count("C"));
        REQUIRE(reachable.count("D"));
      }

      THEN("We expect only {A} to be reachable from {A} in 0 steps")
      {
        irep_idt function_name = "A";
        std::size_t depth = 0;
        std::set<irep_idt> reachable = get_functions_reachable_within_n_steps(
          exported, function_name, depth);
        REQUIRE(reachable.size() == 1);
        REQUIRE(reachable.count("A"));
      }

      THEN("We expect A to have successors {A, B}")
      {
        std::set<irep_idt> successors = get_callees(exported, "A");
        REQUIRE(successors.size() == 2);
        REQUIRE(successors.count("A"));
        REQUIRE(successors.count("B"));
      }

      THEN("We expect C to have predecessors {B}")
      {
        std::set<irep_idt> predecessors = get_callers(exported, "C");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("B"));
      }

      THEN("We expect all of {A, B, C, D} to be reachable from A")
      {
        std::set<irep_idt> successors =
          get_reachable_functions(exported, "A");
        REQUIRE(successors.size() == 4);
        REQUIRE(successors.count("A"));
        REQUIRE(successors.count("B"));
        REQUIRE(successors.count("C"));
        REQUIRE(successors.count("D"));
      }

      THEN("We expect {D, B, A} to be able to reach D")
      {
        std::set<irep_idt> predecessors =
          get_reaching_functions(exported, "D");
        REQUIRE(predecessors.size() == 3);
        REQUIRE(predecessors.count("A"));
        REQUIRE(predecessors.count("B"));
        REQUIRE(predecessors.count("D"));
      }

      THEN("We expect {E} to be able to reach E")
      {
        std::set<irep_idt> predecessors =
          get_reaching_functions(exported, "E");
        REQUIRE(predecessors.size() == 1);
        REQUIRE(predecessors.count("E"));
      }
    }

    WHEN("The call graph, with call sites, is exported as a grapht")
    {
      call_grapht call_graph_from_goto_functions_tracking(goto_model, true);
      call_grapht::directed_grapht exported =
        call_graph_from_goto_functions_tracking.get_directed_graph();

      typedef call_grapht::directed_grapht::node_indext node_indext;
      std::map<irep_idt, node_indext> nodes_by_name;
      for(node_indext i=0; i<exported.size(); ++i)
        nodes_by_name[exported[i].function]=i;

      THEN("We expect 5 nodes")
      {
        REQUIRE(exported.size() == 5);
      }

      THEN("We expect edges A -> { A, B }, B -> { C, D }")
      {
        // Note that means the extra A -> B edge has gone away (the grapht
        // structure can't represent the parallel edge)
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["A"]));
        REQUIRE(exported.has_edge(nodes_by_name["A"], nodes_by_name["B"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["C"]));
        REQUIRE(exported.has_edge(nodes_by_name["B"], nodes_by_name["D"]));
      }

      THEN("We expect all edges to have one callsite apart from A -> B with 2")
      {
        for(node_indext i=0; i<exported.size(); ++i)
        {
          const auto &node=exported[i];
          for(const auto &edge : node.out)
          {
            if(i==nodes_by_name["A"] && edge.first==nodes_by_name["B"])
              REQUIRE(edge.second.callsites.size()==2);
            else
              REQUIRE(edge.second.callsites.size()==1);
          }
        }
      }
    }
  }
}
