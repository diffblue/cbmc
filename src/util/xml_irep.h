/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_XML_IREP_H
#define CPROVER_UTIL_XML_IREP_H

class irept;
class xmlt;

void convert(
  const irept &irep,
  xmlt &xml);

void convert(
  const xmlt &xml,
  irept &irep);

#endif // CPROVER_UTIL_XML_IREP_H
