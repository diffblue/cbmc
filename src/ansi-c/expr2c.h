/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_EXPR2C_H
#define CPROVER_ANSI_C_EXPR2C_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2c(const exprt &expr, const namespacet &ns);
std::string type2c(const typet &type, const namespacet &ns);

#endif // CPROVER_ANSI_C_EXPR2C_H
