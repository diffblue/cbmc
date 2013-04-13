/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMBOL_TABLE_H
#define CPROVER_SYMBOL_TABLE_H

/*! \file util/symbol_table.h
 * \brief Symbol table
 *
 * \author Daniel Kroening <kroening@kroening.com>
*/

/*! \defgroup gr_symbol_table Symbol Table
*/

#include <ostream>
#include <map>

#include "hash_cont.h"
#include "symbol.h"

#define forall_symbols(it, expr) \
  for(symbol_tablet::symbolst::const_iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

#define Forall_symbols(it, expr) \
  for(symbol_tablet::symbolst::iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

typedef std::multimap<irep_idt, irep_idt> symbol_base_mapt;
typedef std::multimap<irep_idt, irep_idt> symbol_module_mapt;

#define forall_symbol_base_map(it, expr, base_name) \
  for(symbol_base_mapt::const_iterator it=(expr).lower_bound(base_name), \
                                       it_end=(expr).upper_bound(base_name); \
      it!=it_end; ++it)

#define forall_symbol_module_map(it, expr, module) \
  for(symbol_module_mapt::const_iterator it=(expr).lower_bound(module), \
                                         it_end=(expr).upper_bound(module); \
      it!=it_end; ++it)

/*! \brief The symbol table
    \ingroup gr_symbol_table
*/
class symbol_tablet
{
public:
  typedef hash_map_cont<irep_idt, symbolt, irep_id_hash> symbolst;

  symbolst symbols;
  symbol_base_mapt symbol_base_map;
  symbol_module_mapt symbol_module_map;
  
  bool add(const symbolt &symbol);
  
  bool move(symbolt &symbol, symbolt *&new_symbol);

  // this will go away, use add instead
  bool move(symbolt &symbol)
  { symbolt *new_symbol; return move(symbol, new_symbol); }
   
  void clear()
  {
    symbols.clear();
    symbol_base_map.clear();
    symbol_module_map.clear();
  }

  bool remove(const irep_idt &name);
   
  void show(std::ostream &out) const;
  
  // deprecated -- will go away
  const irept &value(const irep_idt &name) const;
  
  inline void swap(symbol_tablet &other)
  {
    symbols.swap(other.symbols);
    symbol_base_map.swap(other.symbol_base_map);
    symbol_module_map.swap(other.symbol_module_map);
  }
  
  inline bool has_symbol(const irep_idt &name) const
  {
    return symbols.find(name)!=symbols.end();
  }

  symbolt &lookup(const irep_idt &identifier);
  const symbolt &lookup(const irep_idt &identifier) const;
};

// old name, will go away
class contextt:public symbol_tablet
{
};

std::ostream &operator << (
  std::ostream &out,
  const symbol_tablet &symbol_table);

#endif
