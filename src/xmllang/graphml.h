/*******************************************************************\

Module: Read/write graphs as GraphML

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

/// \file
/// Read/write graphs as GraphML

#ifndef CPROVER_XMLLANG_GRAPHML_H
#define CPROVER_XMLLANG_GRAPHML_H

#include <iosfwd>
#include <string>

#include <util/irep.h>
#include <util/graph.h>
#include <util/xml.h>

struct xml_edget
{
  xmlt xml_node;
};

struct xml_graph_nodet:public graph_nodet<xml_edget>
{
  typedef graph_nodet<xml_edget>::edget edget;
  typedef graph_nodet<xml_edget>::edgest edgest;

  std::string node_name;
  irep_idt file;
  irep_idt line;
  bool is_violation;
  bool has_invariant;
  std::string invariant;
  std::string invariant_scope;
};

class graphmlt:public grapht<xml_graph_nodet>
{
public:
  bool has_node(const std::string &node_name) const
  {
    for(const auto &n : nodes)
      if(n.node_name==node_name)
        return true;

    return false;
  }

  node_indext add_node_if_not_exists(std::string node_name)
  {
    for(node_indext i=0; i<nodes.size(); ++i)
    {
      if(nodes[i].node_name==node_name)
        return i;
    }

    return grapht<xml_graph_nodet>::add_node();
  }

  typedef std::map<std::string, std::string> key_valuest;
  key_valuest key_values;
};

bool read_graphml(
  std::istream &is,
  graphmlt &dest,
  graphmlt::node_indext &entry);
bool read_graphml(
  const std::string &filename,
  graphmlt &dest,
  graphmlt::node_indext &entry);

bool write_graphml(const graphmlt &src, std::ostream &os);

#endif // CPROVER_XMLLANG_GRAPHML_H
