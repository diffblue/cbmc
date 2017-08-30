/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_OPERATORS_H
#define CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_OPERATORS_H

class byte_extract_exprt;
class byte_update_exprt;
class exprt;
class namespacet;

exprt flatten_byte_extract(
  const byte_extract_exprt &src,
  const namespacet &ns);

exprt flatten_byte_update(
  const byte_update_exprt &src,
  const namespacet &ns);

exprt flatten_byte_operators(
  const exprt &src,
  const namespacet &ns);

bool has_byte_operator(const exprt &src);

#endif // CPROVER_SOLVERS_FLATTENING_FLATTEN_BYTE_OPERATORS_H
