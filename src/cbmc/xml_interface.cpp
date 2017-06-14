/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// XML Interface

#include <iostream>

#include <util/message.h>

#include <xmllang/xml_parser.h>

#include "xml_interface.h"

/// XML User Interface
void xml_interfacet::get_xml_options(cmdlinet &cmdline)
{
  if(cmdline.isset("xml-interface"))
  {
    null_message_handlert message_handler;
    xmlt xml;

    parse_xml(std::cin, "", message_handler, xml);

    get_xml_options(xml, cmdline);

    cmdline.set("xml-ui");
  }
}

/// XML User Interface
void xml_interfacet::get_xml_options(
  const xmlt &xml,
  cmdlinet &cmdline)
{
  for(const auto &e : xml.elements)
  {
    // recursive call
    get_xml_options(e, cmdline);
  }

  if(xml.name=="valueOption")
  {
    std::string name=xml.get_attribute("name");
    std::string value=xml.get_attribute("actual");

    if(name=="")
      cmdline.args.push_back(value);
    else
      cmdline.set(name, value);
  }
  else if(xml.name=="flagOption")
  {
    if(xml.get_attribute("actual")=="on")
    {
      cmdline.set(xml.get_attribute("name"));
    }
  }
}
