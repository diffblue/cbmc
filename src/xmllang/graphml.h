/*******************************************************************\

Module: Read/write graphs as GraphML

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

#ifndef CPROVER_XMLLANG_GRAPHML_H
#define CPROVER_XMLLANG_GRAPHML_H

#include <istream>
#include <ostream>
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
  unsigned thread_nr;
  bool is_violation;
};

typedef graph<xml_graph_nodet> graphmlt;

bool read_graphml(
  std::istream &is,
  graphmlt &dest,
  unsigned &entry);
bool read_graphml(
  const std::string &filename,
  graphmlt &dest,
  unsigned &entry);

bool write_graphml(const graphmlt &src, std::ostream &os);

#endif
