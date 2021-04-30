/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#ifndef CPROVER_ANSI_C_PADDING_H
#define CPROVER_ANSI_C_PADDING_H

#include <util/mp_arith.h>

class namespacet;
class struct_typet;
class typet;
class union_typet;

mp_integer alignment(const typet &type, const namespacet &);
void add_padding(struct_typet &type, const namespacet &);
void add_padding(union_typet &type, const namespacet &);

#endif // CPROVER_ANSI_C_PADDING_H
