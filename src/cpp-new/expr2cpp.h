/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_EXPR2CPP_H
#define CPROVER_EXPR2CPP_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2cpp(const exprt &expr, const namespacet &ns);
std::string type2cpp(const typet &type, const namespacet &ns);

#endif
