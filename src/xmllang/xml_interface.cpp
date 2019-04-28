/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// XML Interface

#include "xml_interface.h"

#include <iostream>

#include <util/cmdline.h>
#include <util/message.h>

#include <xmllang/xml_parser.h>

/// Parse commandline options from \p xml into \p cmdline
static void get_xml_options(const xmlt &xml, cmdlinet &cmdline)
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

void xml_interface(cmdlinet &cmdline, message_handlert &message_handler)
{
  if(cmdline.isset("xml-interface"))
  {
    xmlt xml;

    parse_xml(std::cin, "", message_handler, xml);

    get_xml_options(xml, cmdline);

    // Add this so that it gets propagated into optionst;
    // the ui_message_handlert::uit has already been set on the basis
    // of the xml-interface flag.
    cmdline.set("xml-ui");
  }
}
