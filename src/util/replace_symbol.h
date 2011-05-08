/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_REPLACE_SYMBOL_H
#define CPROVER_REPLACE_SYMBOL_H

//
// true: did nothing
// false: replaced something
//

#include "hash_cont.h"
#include "expr.h"

class replace_symbolt
{
public:
  typedef hash_map_cont<irep_idt, exprt, irep_id_hash> expr_mapt;
  typedef hash_map_cont<irep_idt, typet, irep_id_hash> type_mapt;
  
  void insert(const irep_idt &identifier,
              const exprt &expr)
  {
    expr_map.insert(std::pair<irep_idt, exprt>(identifier, expr));
  }
  
  void insert(const irep_idt &identifier,
              const typet &type)
  {
    type_map.insert(std::pair<irep_idt, typet>(identifier, type));
  }
  
  virtual bool replace(exprt &dest) const;
  virtual bool replace(typet &dest) const;

  replace_symbolt();
  virtual ~replace_symbolt();
  
  expr_mapt expr_map;
  type_mapt type_map;

protected:  
  bool have_to_replace(const exprt &dest) const;
  bool have_to_replace(const typet &type) const;
};

#endif
