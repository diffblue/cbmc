/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_EXPR2CPP_H
#define CPROVER_CPP_EXPR2CPP_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2cpp(const exprt &expr, const namespacet &ns);
std::string type2cpp(const typet &type, const namespacet &ns);

#endif // CPROVER_CPP_EXPR2CPP_H
