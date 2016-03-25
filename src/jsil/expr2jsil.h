/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_EXPR2JSIL_H
#define CPROVER_EXPR2JSIL_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2jsil(const exprt &expr, const namespacet &ns);
std::string type2jsil(const typet &type, const namespacet &ns);

#endif
