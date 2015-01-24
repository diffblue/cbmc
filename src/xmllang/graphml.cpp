/*******************************************************************\

Module: Read/write graphs as GraphML

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

#include <cassert>
#include <set>

#include <util/message.h>
#include <util/string2int.h>
#include <util/i2string.h>

#include "graphml.h"

// include last to make sure #define stack(x) of parser.h does not
// collide with std::stack included by graph.h
#include "xml_parser.h"

/*******************************************************************\

Function: add_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static unsigned add_node(
  const std::string &name,
  std::map<std::string, unsigned> &name_to_node,
  graphmlt &graph)
{
  std::pair<std::map<std::string, unsigned>::iterator, bool> entry=
    name_to_node.insert(std::make_pair(name, 0));
  if(entry.second)
    entry.first->second=graph.add_node();

  return entry.first->second;
}

/*******************************************************************\

Function: build_graph_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool build_graph_rec(
  const xmlt &xml,
  std::map<std::string, unsigned> &name_to_node,
  std::set<std::string> &sinks,
  graphmlt &dest,
  std::string &entrynode)
{
  if(xml.name=="node")
  {
    const std::string node_name=xml.get_attribute("id");

    for(xmlt::elementst::const_iterator
        e_it=xml.elements.begin();
        e_it!=xml.elements.end();
        e_it++)
      if(e_it->get_attribute("key")=="sink" &&
         e_it->data=="true")
      {
        assert(name_to_node.find(node_name)==name_to_node.end());
        sinks.insert(node_name);
        return false;
      }

    const unsigned n=add_node(node_name, name_to_node, dest);

    graphmlt::nodet &node=dest[n];
    node.node_name=node_name;
    node.is_violation=false;
    node.thread_nr=0;

    for(xmlt::elementst::const_iterator
        e_it=xml.elements.begin();
        e_it!=xml.elements.end();
        e_it++)
      if(e_it->get_attribute("key")=="violation" &&
         e_it->data=="true")
        node.is_violation=e_it->data=="true";
      else if(e_it->get_attribute("key")=="threadNumber")
        node.thread_nr=safe_string2unsigned(e_it->data);
  }
  else if(xml.name=="edge")
  {
    const std::string source=xml.get_attribute("source");
    const std::string target=xml.get_attribute("target");

    assert(sinks.find(source)==sinks.end());
    if(sinks.find(target)!=sinks.end())
      return false;

    const unsigned s=add_node(source, name_to_node, dest);
    const unsigned t=add_node(target, name_to_node, dest);

    // add edge and annotate
    dest[s].out[t].xml_node=xml;
    dest[t].in[s].xml_node=xml;
  }
  else if(xml.name=="graphml" ||
          xml.name=="graph" ||
          xml.name=="data")
  {
    for(xmlt::elementst::const_iterator
        e_it=xml.elements.begin();
        e_it!=xml.elements.end();
        e_it++)
      // recursive call
      if(build_graph_rec(*e_it, name_to_node, sinks, dest, entrynode))
        return true;

    if(xml.name=="data" &&
       xml.get_attribute("key")=="entrynode")
      entrynode=xml.data;
  }
  else if(xml.name=="key")
  {
    // ignored
  }
  else
  {
    assert(false);
    return true;
  }

  return false;
}

/*******************************************************************\

Function: build_graph

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool build_graph(
  const xmlt &xml,
  graphmlt &dest,
  unsigned &entry)
{
  assert(dest.size()==0);

  std::map<std::string, unsigned> name_to_node;
  std::set<std::string> sinks;
  std::string entrynode;

  const bool err=
    build_graph_rec(xml, name_to_node, sinks, dest, entrynode);

  for(unsigned i=0; !err && i<dest.size(); ++i)
  {
    const graphmlt::nodet &n=dest[i];

    assert(!n.node_name.empty());
  }

  assert(!entrynode.empty());
  std::map<std::string, unsigned>::const_iterator it=
    name_to_node.find(entrynode);
  assert(it!=name_to_node.end());
  entry=it->second;

  return err;
}

/*******************************************************************\

Function: read_graphml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool read_graphml(std::istream &is, graphmlt &dest, unsigned &entry)
{
  null_message_handlert message_handler;
  xmlt xml;

  if(parse_xml(is, "", message_handler, xml))
    return true;

  return build_graph(xml, dest, entry);
}

/*******************************************************************\

Function: read_graphml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool read_graphml(
  const std::string &filename,
  graphmlt &dest,
  unsigned &entry)
{
  null_message_handlert message_handler;
  xmlt xml;

  if(parse_xml(filename, message_handler, xml))
    return true;

  return build_graph(xml, dest, entry);
}

/*******************************************************************\

Function: write_graphml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool write_graphml(const graphmlt &src, std::ostream &os)
{
  xmlt graphml("graphml");
  graphml.set_attribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
  graphml.set_attribute("xmlns", "http://graphml.graphdrawing.org/xmlns");

  // <key attr.name="assumption" attr.type="string" for="edge" id="assumption"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "assumption");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "assumption");
  }

  // <key attr.name="sourcecode" attr.type="string" for="edge" id="sourcecode"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "sourcecode");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "sourcecode");
  }

  // <key attr.name="sourcecodeLanguage" attr.type="string" for="graph" id="sourcecodelang"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "sourcecodeLanguage");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "graph");
    key.set_attribute("id", "sourcecodelang");
  }

  // <key attr.name="tokenSet" attr.type="string" for="edge" id="tokens"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "tokenSet");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "tokens");
  }

  // <key attr.name="originTokenSet" attr.type="string" for="edge" id="origintokens"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "originTokenSet");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "origintokens");
  }

  // <key attr.name="negativeCase" attr.type="string" for="edge" id="negated">
  //     <default>false</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "negativeCase");
    key.set_attribute("attr.type", "boolean");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "negated");

    key.new_element("default").data="false";
  }

  // <key attr.name="lineNumberInOrigin" attr.type="int" for="edge" id="originline"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "lineNumberInOrigin");
    key.set_attribute("attr.type", "int");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "originline");
  }

  // <key attr.name="originFileName" attr.type="string" for="edge" id="originfile">
  //     <default>"&lt;command-line&gt;"</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "originFileName");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "originfile");

    key.new_element("default").data="\"<command-line>\"";
  }

  // <key attr.name="nodeType" attr.type="string" for="node" id="nodetype">
  //     <default>path</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "nodeType");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "node");
    key.set_attribute("id", "nodetype");

    key.new_element("default").data="path";
  }

  // <key attr.name="isFrontierNode" attr.type="boolean" for="node" id="frontier">
  //     <default>false</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "isFrontierNode");
    key.set_attribute("attr.type", "boolean");
    key.set_attribute("for", "node");
    key.set_attribute("id", "frontier");

    key.new_element("default").data="false";
  }

  // <key attr.name="isViolationNode" attr.type="boolean" for="node" id="violation">
  //     <default>false</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "isViolationNode");
    key.set_attribute("attr.type", "boolean");
    key.set_attribute("for", "node");
    key.set_attribute("id", "violation");

    key.new_element("default").data="false";
  }

  // <key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry">
  //     <default>false</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "isEntryNode");
    key.set_attribute("attr.type", "boolean");
    key.set_attribute("for", "node");
    key.set_attribute("id", "entry");

    key.new_element("default").data="false";
  }

  // <key attr.name="isSinkNode" attr.type="boolean" for="node" id="sink">
  //     <default>false</default>
  // </key>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "isSinkNode");
    key.set_attribute("attr.type", "boolean");
    key.set_attribute("for", "node");
    key.set_attribute("id", "sink");

    key.new_element("default").data="false";
  }

  // <key attr.name="enterFunction" attr.type="string" for="edge" id="enterFunction"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "enterFunction");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "enterFunction");
  }

  // <key attr.name="returnFromFunction" attr.type="string" for="edge" id="returnFrom"/>
  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "returnFromFunction");
    key.set_attribute("attr.type", "string");
    key.set_attribute("for", "edge");
    key.set_attribute("id", "returnFrom");
  }

  {
    xmlt &key=graphml.new_element("key");
    key.set_attribute("attr.name", "threadNumber");
    key.set_attribute("attr.type", "int");
    key.set_attribute("for", "node");
    key.set_attribute("id", "thread");

    key.new_element("default").data="0";
  }


  xmlt &graph=graphml.new_element("graph");
  graph.set_attribute("edgedefault", "directed");

  // <data key="sourcecodelang">C</data>
  {
    xmlt &data=graph.new_element("data");
    data.set_attribute("key", "sourcecodelang");
    data.data="C";
  }

  bool entry_done=false;
  for(unsigned i=0; i<src.size(); ++i)
  {
    const graphmlt::nodet &n=src[i];

    // <node id="A12"/>
    xmlt &node=graph.new_element("node");
    node.set_attribute("id", n.node_name);

    // <node id="A1">
    //     <data key="entry">true</data>
    // </node>
    if(!entry_done && n.node_name!="sink")
    {
      xmlt &entry=node.new_element("data");
      entry.set_attribute("key", "entry");
      entry.data="true";

      entry_done=true;
    }

    if(n.thread_nr!=0)
    {
      xmlt &entry=node.new_element("data");
      entry.set_attribute("key", "threadNumber");
      entry.data=i2string(n.thread_nr);
    }

    // <node id="A14">
    //     <data key="violation">true</data>
    // </node>
    if(n.is_violation)
    {
      xmlt &entry=node.new_element("data");
      entry.set_attribute("key", "violation");
      entry.data="true";
    }

    for(graphmlt::edgest::const_iterator
        e_it=n.out.begin();
        e_it!=n.out.end();
        ++e_it)
      graph.new_element(e_it->second.xml_node);
  }

  os << "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n";
  os << graphml;

  return !os.good();
}

