/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_RENAME_SYMBOL_H
#define CPROVER_UTIL_RENAME_SYMBOL_H

//
// true: did nothing
// false: renamed something
//

#include <unordered_map>

#include "irep.h"

class exprt;
class typet;

class rename_symbolt
{
public:
  typedef std::unordered_map<irep_idt, irep_idt> expr_mapt;
  typedef std::unordered_map<irep_idt, irep_idt> type_mapt;

  void insert_expr(const irep_idt &old_id,
                   const irep_idt &new_id)
  {
    expr_map.insert(std::pair<irep_idt, irep_idt>(old_id, new_id));
  }

  void insert(const class symbol_exprt &old_expr,
              const class symbol_exprt &new_expr);

  void insert_type(const irep_idt &old_id,
                   const irep_idt &new_id)
  {
    type_map.insert(std::pair<irep_idt, irep_idt>(old_id, new_id));
  }

  /// Rename symbols in \p dest.
  /// \return True if, and only if, the expression was not modified.
  bool operator()(exprt &dest) const
  {
    return rename(dest);
  }

  /// Rename symbols in \p dest.
  /// \return True if, and only if, the type was not modified.
  bool operator()(typet &dest) const
  {
    return rename(dest);
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

#endif // CPROVER_UTIL_RENAME_SYMBOL_H
