/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_EXPR2JSIL_H
#define CPROVER_JSIL_EXPR2JSIL_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2jsil(const exprt &expr, const namespacet &ns);
std::string type2jsil(const typet &type, const namespacet &ns);

#endif // CPROVER_JSIL_EXPR2JSIL_H
