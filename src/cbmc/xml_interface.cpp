/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <message.h>

#include <xmllang/xml_parser.h>

#include "xml_interface.h"

/*******************************************************************\

Function: xml_interfacet::get_xml_options

  Inputs:

 Outputs:

 Purpose: XML User Interface

\*******************************************************************/

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

/*******************************************************************\

Function: xml_interfacet::get_xml_options

  Inputs:

 Outputs:

 Purpose: XML User Interface

\*******************************************************************/

void xml_interfacet::get_xml_options(
  const xmlt &xml,
  cmdlinet &cmdline)
{
  for(xmlt::elementst::const_iterator
      e_it=xml.elements.begin();
      e_it!=xml.elements.end();
      e_it++)
  {
    // recursive call
    get_xml_options(*e_it, cmdline);
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

