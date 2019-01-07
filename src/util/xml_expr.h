/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_XML_EXPR_H
#define CPROVER_UTIL_XML_EXPR_H

#include "xml.h"

class typet;
class exprt;
class namespacet;

xmlt xml(
  const exprt &,
  const namespacet &);

xmlt xml(
  const typet &,
  const namespacet &);

#endif // CPROVER_UTIL_XML_EXPR_H
