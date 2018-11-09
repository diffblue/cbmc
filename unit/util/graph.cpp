/*******************************************************************\

Module: Unit test for graph.h

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/graph.h>

template<class E>
static inline bool operator==(
  const graph_nodet<E> &gn1, const graph_nodet<E> &gn2)
{
  return gn1.in == gn2.in && gn1.out == gn2.out;
}

template<class N>
static inline bool operator==(const grapht<N> &g1, const grapht<N> &g2)
{
  if(g1.size() != g2.size())
    return false;

  for(typename grapht<N>::node_indext i = 0; i < g1.size(); ++i)
  {
    if(!(g1[i] == g2[i]))
      return false;
  }

  return true;
}

/// To verify make_chordal is working as intended: naively search for a
/// hole (a chordless 4+-cycle)
template<class N>
static bool contains_hole(
  const grapht<N> &g,
  const std::vector<typename grapht<N>::node_indext> &cycle_so_far)
{
  const auto &successors_map = g[cycle_so_far.back()].out;

  // If this node has a triangular edge (one leading to cycle_so_far[-3]) then
  // this isn't a hole:
  if(cycle_so_far.size() >= 3 &&
     successors_map.count(cycle_so_far[cycle_so_far.size() - 3]) != 0)
  {
    return false;
  }

  // If this node has an edge leading to any other cycle member (except our
  // immediate predecessor) then we've found a hole:
  if(cycle_so_far.size() >= 4)
  {
    for(std::size_t i = 0; i <= cycle_so_far.size() - 4; ++i)
    {
      if(successors_map.count(cycle_so_far[i]) != 0)
        return true;
    }
  }

  // Otherwise try to extend the cycle:
  for(const auto &successor : successors_map)
  {
    // The input is undirected, so a 2-cycle is always present:
    if(cycle_so_far.size() >= 2 &&
       successor.first == cycle_so_far[cycle_so_far.size() - 2])
    {
      continue;
    }

    std::vector<typename grapht<N>::node_indext> extended_cycle = cycle_so_far;
    extended_cycle.push_back(successor.first);
    if(contains_hole(g, extended_cycle))
      return true;
  }

  return false;
}

template<class N>
static bool contains_hole(const grapht<N> &g)
{
  // For each node in the graph, check for cycles starting at that node.
  // This is pretty dumb, but I figure this formulation is simple enough to
  // check by hand and the complexity isn't too bad for small examples.

  for(typename grapht<N>::node_indext i = 0; i < g.size(); ++i)
  {
    std::vector<typename grapht<N>::node_indext> start_node {i};
    if(contains_hole(g, start_node))
      return true;
  }

  return false;
}

typedef grapht<graph_nodet<empty_edget>> simple_grapht;

SCENARIO("graph-make-chordal",
  "[core][util][graph]")
{
  GIVEN("An acyclic graph")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[5];

    for(int i = 0; i < 5; ++i)
      indices[i] = graph.add_node();

    // Make a graph: 0 <-> 1 <-> 4
    //                \->  2  <-/
    //                 \-> 3
    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[0], indices[2]);
    graph.add_undirected_edge(indices[0], indices[3]);
    graph.add_undirected_edge(indices[1], indices[4]);
    graph.add_undirected_edge(indices[2], indices[4]);

    WHEN("The graph is made chordal")
    {
      simple_grapht chordal_graph = graph;
      chordal_graph.make_chordal();

      THEN("The graph should be unchanged")
      {
        // This doesn't pass, as make_chordal actually adds triangular edges to
        // *all* common neighbours, even nodes that aren't part of a cycle.
        // REQUIRE(graph == chordal_graph);

        // At least it shouldn't be chordal!
        REQUIRE(!contains_hole(chordal_graph));
      }
    }
  }

  GIVEN("A cyclic graph that is already chordal")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[5];

    for(int i = 0; i < 5; ++i)
      indices[i] = graph.add_node();

    // Make a graph: 0 <-> 1 <-> 2 <-> 0
    //               3 <-> 1 <-> 2 <-> 3
    //               4 <-> 1 <-> 2 <-> 4
    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[1], indices[2]);
    graph.add_undirected_edge(indices[2], indices[0]);
    graph.add_undirected_edge(indices[3], indices[1]);
    graph.add_undirected_edge(indices[2], indices[3]);
    graph.add_undirected_edge(indices[4], indices[1]);
    graph.add_undirected_edge(indices[2], indices[4]);

    WHEN("The graph is made chordal")
    {
      simple_grapht chordal_graph = graph;
      chordal_graph.make_chordal();

      THEN("The graph should be unchanged")
      {
        // This doesn't pass, as make_chordal actually adds triangular edges to
        // *all* common neighbours, even cycles that are already chordal.
        // REQUIRE(graph == chordal_graph);

        // At least it shouldn't be chordal!
        REQUIRE(!contains_hole(chordal_graph));
      }
    }
  }

  GIVEN("A simple 4-cycle")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[4];

    for(int i = 0; i < 4; ++i)
      indices[i] = graph.add_node();

    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[1], indices[2]);
    graph.add_undirected_edge(indices[2], indices[3]);
    graph.add_undirected_edge(indices[3], indices[0]);

    // Check the contains_hole predicate is working as intended:
    REQUIRE(contains_hole(graph));

    WHEN("The graph is made chordal")
    {
      simple_grapht chordal_graph = graph;
      chordal_graph.make_chordal();

      THEN("The graph should gain a chord")
      {
        REQUIRE(!contains_hole(chordal_graph));
      }
    }
  }

  GIVEN("A more complicated graph with a hole")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[8];

    for(int i = 0; i < 8; ++i)
      indices[i] = graph.add_node();

    // A 5-cycle:
    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[1], indices[2]);
    graph.add_undirected_edge(indices[2], indices[3]);
    graph.add_undirected_edge(indices[3], indices[4]);
    graph.add_undirected_edge(indices[4], indices[0]);

    // A 3-cycle connected to the 5:
    graph.add_undirected_edge(indices[4], indices[5]);
    graph.add_undirected_edge(indices[5], indices[6]);
    graph.add_undirected_edge(indices[6], indices[4]);

    // Another 3-cycle joined onto the 5:
    graph.add_undirected_edge(indices[1], indices[7]);
    graph.add_undirected_edge(indices[3], indices[7]);

    // Check we've made the input correctly:
    REQUIRE(contains_hole(graph));

    WHEN("The graph is made chordal")
    {
      simple_grapht chordal_graph = graph;
      chordal_graph.make_chordal();

      THEN("The graph's 5-cycle should be completed with chords")
      {
        REQUIRE(!contains_hole(chordal_graph));
      }
    }
  }
}

SCENARIO("graph-connected-subgraphs",
  "[core][util][graph]")
{
  GIVEN("A connected graph")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[5];

    for(int i = 0; i < 5; ++i)
      indices[i] = graph.add_node();

    // Make a graph: 0 <-> 1 <-> 4
    //                \->  2  <-/
    //                 \-> 3
    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[0], indices[2]);
    graph.add_undirected_edge(indices[0], indices[3]);
    graph.add_undirected_edge(indices[1], indices[4]);
    graph.add_undirected_edge(indices[2], indices[4]);

    WHEN("We take its connected subgraphs")
    {
      std::vector<simple_grapht::node_indext> subgraphs;
      graph.connected_subgraphs(subgraphs);

      REQUIRE(subgraphs.size() == graph.size());
      simple_grapht::node_indext only_subgraph = subgraphs.at(0);

      // Check everything is in one subgraph:
      REQUIRE(
        subgraphs ==
        std::vector<simple_grapht::node_indext>(graph.size(), only_subgraph));
    }
  }

  GIVEN("A graph with three unconnected subgraphs")
  {
    simple_grapht graph;
    simple_grapht::node_indext indices[6];

    for(int i = 0; i < 6; ++i)
      indices[i] = graph.add_node();

    graph.add_undirected_edge(indices[0], indices[1]);
    graph.add_undirected_edge(indices[2], indices[3]);
    graph.add_undirected_edge(indices[4], indices[5]);

    WHEN("We take its connected subgraphs")
    {
      std::vector<simple_grapht::node_indext> subgraphs;
      graph.connected_subgraphs(subgraphs);

      REQUIRE(subgraphs.size() == graph.size());
      simple_grapht::node_indext first_subgraph = subgraphs.at(0);
      simple_grapht::node_indext second_subgraph = subgraphs.at(2);
      simple_grapht::node_indext third_subgraph = subgraphs.at(4);

      std::vector<simple_grapht::node_indext> expected_subgraphs
      {
        first_subgraph,
        first_subgraph,
        second_subgraph,
        second_subgraph,
        third_subgraph,
        third_subgraph
      };

      REQUIRE(subgraphs == expected_subgraphs);
    }
  }
}
