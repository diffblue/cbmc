/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_XML_EXPR_H
#define CPROVER_GOTO_PROGRAMS_XML_EXPR_H

#include <util/xml.h>

class typet;
class exprt;
class namespacet;

xmlt xml(const exprt &, const namespacet &);

xmlt xml(const typet &, const namespacet &);

#endif // CPROVER_GOTO_PROGRAMS_XML_EXPR_H
