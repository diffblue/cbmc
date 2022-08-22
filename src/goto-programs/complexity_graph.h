


class complexity_grapht 
{
 public:

  class nodet {
  public:

    enum class node_typet {FUNCTION, LOOP, FUNCTION_POINTER};

    irep_idt name;
    std::string display_name;
    node_typet node_type;
    std::set<irep_idt> properties;
    std::vector<std::vector<goto_programt::const_targett>> instructions;

    int indegree;
    int outdegree;

    nodet (const irep_idt name_,
           const std::string &display_name_,
           node_typet node_type_
           ) {

      name = name_;
      display_name = display_name_;
      node_type = node_type_;
    }

    //void make_info(...);

    void add_property (const irep_idt &key) {
      properties.insert (key);
    }

    const bool has_property (const irep_idt &key) const {
      return properties.find (key) != properties.end();
    }

  };
  
  class edget {

  public:

    irep_idt node1;
    irep_idt node2;
    std::set<irep_idt> properties;

    edget (const irep_idt node1_,
           const irep_idt node2_) {

      node1 = node1_;
      node2 = node2_;
    }

    void add_property (const irep_idt key) {
      properties.insert (key);
    }

    const bool has_property (const irep_idt key) {
      return properties.find (key) != properties.end();
    }

  };

  std::map<irep_idt, nodet> node_map;
  std::map<irep_idt, std::map<irep_idt, edget>> edge_map;
  std::map<irep_idt, std::map<irep_idt, edget>> dual_edge_map;

  complexity_grapht () {

  }

  nodet &add_node (const nodet node) {
    node_map.insert ({node.name, node});
    edge_map.insert ({node.name, std::map<irep_idt, edget>()});
    dual_edge_map.insert ({node.name, std::map<irep_idt, edget>()});
    return node_map.find (node.name)->second;
  }

  const nodet &find_node (const irep_idt &name) const {
    return node_map.find (name)->second;
  }

  const bool has_node (const irep_idt &name) const {
    return (node_map.find (name) != node_map.end());
  }

  edget& add_edge (const irep_idt &name1, const irep_idt &name2) {
    nodet node1 = find_node (name1);
    nodet node2 = find_node (name2);

    node1.outdegree++;
    node2.indegree++;

    const auto &found = edge_map.find (name1);
    std::map<irep_idt, edget> &edge_map2 = found->second;
    const auto &found2 = edge_map2.find (name2);
    if (found2 == edge_map2.end()) {
      edge_map2.insert({name2, edget(name1, name2)});
    }

    {
      const auto &found = dual_edge_map.find (name2);
      std::map<irep_idt, edget> &edge_map2 = found->second;
      const auto &found2 = edge_map2.find (name1);
      if (found2 == edge_map2.end()) {
        edge_map2.insert({name1, edget(name2, name1)});
      }
    }

    return edge_map2.find(name1)->second;
  }


};
