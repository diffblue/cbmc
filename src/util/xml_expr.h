/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_EXPR_H
#define CPROVER_XML_EXPR_H

class source_locationt;
class typet;
class exprt;
class xmlt;
class namespacet;

xmlt xml(
  const exprt &,
  const namespacet &);

xmlt xml(
  const typet &,
  const namespacet &);

xmlt xml(const source_locationt &);

#endif
