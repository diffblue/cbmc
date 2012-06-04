/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FIND_SYMBOLS_H
#define CPROVER_FIND_SYMBOLS_H

#include <set>

#include "hash_cont.h"
#include "irep.h"

class exprt;
class typet;

typedef hash_set_cont<irep_idt, irep_id_hash> find_symbols_sett;

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest);

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  bool current,
  bool next);

void find_symbols(
  const exprt &src,
  std::set<exprt> &dest);
  
bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols);  

void find_type_symbols(
  const typet &src,
  find_symbols_sett &dest);

void find_type_symbols(
  const exprt &src,
  find_symbols_sett &dest);

void find_type_and_expr_symbols(
  const typet &src,
  find_symbols_sett &dest);

void find_type_and_expr_symbols(
  const exprt &src,
  find_symbols_sett &dest);

#endif
