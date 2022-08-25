/*******************************************************************\

Module: Provides the graph datatype for the complexity call graph

Author: Benjamin Quiring

\*******************************************************************/

/// \file
/// Provides the graph datatype for the complexity call graph

class complexity_grapht
{
 public:

  // a class for nodes
  class nodet
  {
  public:

    // the different types for nodes
    enum class node_typet {FUNCTION, LOOP, FUNCTION_POINTER};

    // the name of this node
    irep_idt name;

    // the display name of this node
    std::string display_name;

    // the type of this node
    node_typet node_type;

    // the properties this node has
    std::set<irep_idt> properties;

    // the collection of instructions this node owns
    std::vector<std::vector<goto_programt::const_targett>> instructions;

    // the indegree of this node
    int indegree;

    // the outdegree of this node
    int outdegree;

    // The constructor for nodes.
    nodet (const irep_idt name_, const std::string &display_name_, node_typet node_type_)
    {
      name = name_;
      display_name = display_name_;
      node_type = node_type_;
    }

    // Adds a property to a node.
    void add_property (const irep_idt &key)
    {
      properties.insert (key);
    }

    // Checks if a node has a property
    const bool has_property (const irep_idt &key) const
    {
      return properties.find (key) != properties.end();
    }

  };

  // A class for edges in the graph
  class edget
  {

  public:

    // the 'from' edge
    irep_idt node1;

    // the 'to' edge
    irep_idt node2;

    // properties this edge has
    std::set<irep_idt> properties;

    // Constructor for edges
    edget (const irep_idt node1_, const irep_idt node2_)
    {
      node1 = node1_;
      node2 = node2_;
    }

    // Adds a property to this edge
    void add_property (const irep_idt key)
    {
      properties.insert (key);
    }

    // Checks if this edge has a property
    const bool has_property (const irep_idt key)
    {
      return properties.find (key) != properties.end();
    }

  };

  // The map from names to nodes for this graph
  std::map<irep_idt, nodet> node_map;

  // The map from names to names to edges for this graph
  std::map<irep_idt, std::map<irep_idt, edget>> edge_map;

  // The dual map of edge_map
  std::map<irep_idt, std::map<irep_idt, edget>> dual_edge_map;

  complexity_grapht ()
  {

  }

  // Adds a node to the graph
  nodet &add_node (const nodet node)
  {
    node_map.insert ({node.name, node});
    edge_map.insert ({node.name, std::map<irep_idt, edget>()});
    dual_edge_map.insert ({node.name, std::map<irep_idt, edget>()});
    return node_map.find (node.name)->second;
  }

  // Finds a node in the graph
  const nodet &find_node (const irep_idt &name) const
  {
    return node_map.find (name)->second;
  }

  // Checks if the graph has a node with this name
  const bool has_node (const irep_idt &name) const
  {
    return (node_map.find (name) != node_map.end());
  }

  // Adds an edge to the graph
  edget& add_edge (const irep_idt &name1, const irep_idt &name2)
  {
    nodet node1 = find_node (name1);
    nodet node2 = find_node (name2);

    node1.outdegree++;
    node2.indegree++;

    const auto &found = edge_map.find (name1);
    std::map<irep_idt, edget> &edge_map2 = found->second;
    const auto &found2 = edge_map2.find (name2);
    if (found2 == edge_map2.end())
    {
      edge_map2.insert({name2, edget(name1, name2)});
    }

    {
      const auto &found = dual_edge_map.find (name2);
      std::map<irep_idt, edget> &edge_map2 = found->second;
      const auto &found2 = edge_map2.find (name1);
      if (found2 == edge_map2.end())
      {
        edge_map2.insert({name1, edget(name2, name1)});
      }
    }

    return edge_map2.find(name1)->second;
  }

};
