/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FIND_SYMBOLS_H
#define CPROVER_UTIL_FIND_SYMBOLS_H

#include <set>
#include <unordered_set>

#include "deprecate.h"
#include "irep.h"

class exprt;
class symbol_exprt;
class typet;

typedef std::unordered_set<irep_idt> find_symbols_sett;

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest);

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  bool current,
  bool next);

/// Find sub expressions with id ID_symbol or ID_next_symbol
DEPRECATED(SINCE(2019, 06, 17, "Unused"))
void find_symbols(
  const exprt &src,
  std::set<exprt> &dest);

void find_symbols(
  const exprt &src,
  std::set<symbol_exprt> &dest);

std::set<symbol_exprt> find_symbols(const exprt &src);

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols);

void find_type_symbols(
  const typet &src,
  find_symbols_sett &dest);

void find_type_symbols(
  const exprt &src,
  find_symbols_sett &dest);

void find_non_pointer_type_symbols(
  const typet &src,
  find_symbols_sett &dest);

void find_non_pointer_type_symbols(
  const exprt &src,
  find_symbols_sett &dest);

void find_type_and_expr_symbols(
  const typet &src,
  find_symbols_sett &dest);

void find_type_and_expr_symbols(
  const exprt &src,
  find_symbols_sett &dest);

#endif // CPROVER_UTIL_FIND_SYMBOLS_H
