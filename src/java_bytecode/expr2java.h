/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_EXPR2JAVA_H
#define CPROVER_EXPR2JAVA_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2java(const exprt &expr, const namespacet &ns);
std::string type2java(const typet &type, const namespacet &ns);

#endif
