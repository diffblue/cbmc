/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef XML_IREP_H
#define XML_IREP_H

#include "xml.h"
#include "irep.h"

void convert(
  const irept &irep,
  xmlt &xml);
  
void convert(
  const xmlt &xml,
  irept &irep);

#endif
