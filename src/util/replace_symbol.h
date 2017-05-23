/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_REPLACE_SYMBOL_H
#define CPROVER_UTIL_REPLACE_SYMBOL_H

//
// true: did nothing
// false: replaced something
//

#include "expr.h"

class replace_symbolt
{
public:
  typedef std::unordered_map<irep_idt, exprt, irep_id_hash> expr_mapt;
  typedef std::unordered_map<irep_idt, typet, irep_id_hash> type_mapt;

  void insert(const irep_idt &identifier,
                     const exprt &expr)
  {
    expr_map.insert(std::pair<irep_idt, exprt>(identifier, expr));
  }

  void insert(const class symbol_exprt &old_expr,
              const exprt &new_expr);

  void insert(const irep_idt &identifier,
                     const typet &type)
  {
    type_map.insert(std::pair<irep_idt, typet>(identifier, type));
  }

  virtual bool replace(exprt &dest) const;
  virtual bool replace(typet &dest) const;

  void operator()(exprt &dest) const
  {
    replace(dest);
  }

  void operator()(typet &dest) const
  {
    replace(dest);
  }

  void clear()
  {
    expr_map.clear();
    type_map.clear();
  }

  bool empty() const
  {
    return expr_map.empty() && type_map.empty();
  }

  replace_symbolt();
  virtual ~replace_symbolt();

  expr_mapt expr_map;
  type_mapt type_map;

protected:
  bool have_to_replace(const exprt &dest) const;
  bool have_to_replace(const typet &type) const;
};

#endif // CPROVER_UTIL_REPLACE_SYMBOL_H
