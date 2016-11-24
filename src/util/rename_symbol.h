/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_RENAME_SYMBOL_H
#define CPROVER_RENAME_SYMBOL_H

//
// true: did nothing
// false: renamed something
//

#include "hash_cont.h"
#include "expr.h"

class rename_symbolt
{
public:
  typedef hash_map_cont<irep_idt, irep_idt, irep_id_hash> expr_mapt;
  typedef hash_map_cont<irep_idt, irep_idt, irep_id_hash> type_mapt;
  
  inline void insert_expr(const irep_idt &old_id,
                          const irep_idt &new_id)
  {
    expr_map.insert(std::pair<irep_idt, irep_idt>(old_id, new_id));
  }
  
  void insert(const class symbol_exprt &old_expr,
              const class symbol_exprt &new_expr);

  inline void insert_type(const irep_idt &old_id,
                          const irep_idt &new_id)
  {
    type_map.insert(std::pair<irep_idt, irep_idt>(old_id, new_id));
  }
  
  inline void operator()(exprt &dest) const
  {
    rename(dest);
  }

  inline void operator()(typet &dest) const
  {
    rename(dest);
  }

  rename_symbolt();
  virtual ~rename_symbolt();
  
  expr_mapt expr_map;
  type_mapt type_map;

protected:  
  bool rename(exprt &dest) const;
  bool rename(typet &dest) const;
  
  bool have_to_rename(const exprt &dest) const;
  bool have_to_rename(const typet &type) const;
};

#endif
