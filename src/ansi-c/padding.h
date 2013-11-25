/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_PADDING_H
#define CPROVER_ANSI_C_PADDING_H

#include <util/std_types.h>
#include <util/namespace.h>

unsigned alignment(const typet &type, const namespacet &ns);
void add_padding(struct_typet &type, const namespacet &ns);

#endif
