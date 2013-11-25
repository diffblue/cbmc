/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_EXPR_H
#define CPROVER_XML_EXPR_H

class locationt;
class exprt;
class xmlt;
class namespacet;

xmlt xml(
  const exprt &expr,
  const namespacet &ns);

xmlt xml(const locationt &location);

#endif
