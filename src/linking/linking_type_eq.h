/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_TYPE_EQ_H
#define CPROVER_LINKING_TYPE_EQ_H

bool linking_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns);

#endif
