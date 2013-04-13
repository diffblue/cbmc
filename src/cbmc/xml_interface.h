/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_INTERFACE_H
#define CPROVER_XML_INTERFACE_H

#include <util/cmdline.h>

class xml_interfacet
{
public:
  xml_interfacet(cmdlinet &_cmdline)
  {
    get_xml_options(_cmdline);
  }
  
protected:
  void get_xml_options(cmdlinet &cmdline);
  void get_xml_options(const class xmlt &xml, cmdlinet &cmdline);
};

#endif
