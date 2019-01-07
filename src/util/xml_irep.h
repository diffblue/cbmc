/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_XML_IREP_H
#define CPROVER_UTIL_XML_IREP_H

#include "xml.h"

class irept;
class source_locationt;

void convert(
  const irept &irep,
  xmlt &xml);

void convert(
  const xmlt &xml,
  irept &irep);

xmlt xml(const source_locationt &);

#endif // CPROVER_UTIL_XML_IREP_H
