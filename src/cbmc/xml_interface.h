/*******************************************************************\

Module: XML Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// XML Interface

#ifndef CPROVER_CBMC_XML_INTERFACE_H
#define CPROVER_CBMC_XML_INTERFACE_H

#include <util/cmdline.h>

class xmlt;

class xml_interfacet
{
public:
  explicit xml_interfacet(cmdlinet &_cmdline)
  {
    get_xml_options(_cmdline);
  }

protected:
  void get_xml_options(cmdlinet &cmdline);
  void get_xml_options(const xmlt &xml, cmdlinet &cmdline);
};

#endif // CPROVER_CBMC_XML_INTERFACE_H
