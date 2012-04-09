/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_EXPR_H
#define CPROVER_XML_EXPR_H

class exprt;
class xmlt;
class namespacet;

xmlt convert(
  const exprt &expr,
  const namespacet &ns);

#endif
