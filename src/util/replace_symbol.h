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

#include <unordered_map>

/// Replace expression or type symbols by an expression or type, respectively.
/// The resolved type of the symbol must match the type of the replacement.
class replace_symbolt
{
public:
  typedef std::unordered_map<irep_idt, exprt> expr_mapt;

  /// Sets old_expr to be replaced by new_expr if we don't already have a
  /// replacement; otherwise does nothing (i.e. std::map::insert-like
  /// behaviour).
  void insert(const class symbol_exprt &old_expr,
              const exprt &new_expr);

  /// Sets old_expr to be replaced by new_expr
  void set(const class symbol_exprt &old_expr, const exprt &new_expr);

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
  }

  bool empty() const
  {
    return expr_map.empty();
  }

  std::size_t erase(const irep_idt &id)
  {
    return expr_map.erase(id);
  }

  expr_mapt::iterator erase(expr_mapt::iterator it)
  {
    return expr_map.erase(it);
  }

  bool replaces_symbol(const irep_idt &id) const
  {
    return expr_map.find(id) != expr_map.end();
  }

  replace_symbolt();
  virtual ~replace_symbolt();

  const expr_mapt &get_expr_map() const
  {
    return expr_map;
  }

  expr_mapt &get_expr_map()
  {
    return expr_map;
  }

protected:
  expr_mapt expr_map;

  virtual bool replace_symbol_expr(symbol_exprt &dest) const;

  bool have_to_replace(const exprt &dest) const;
  bool have_to_replace(const typet &type) const;
};

class unchecked_replace_symbolt : public replace_symbolt
{
public:
  unchecked_replace_symbolt()
  {
  }

  void insert(const symbol_exprt &old_expr, const exprt &new_expr);

protected:
  bool replace_symbol_expr(symbol_exprt &dest) const override;
};

/// Replace symbols with constants while maintaining syntactically valid
/// expressions.
/// If you are replacing symbols with constants in an l-value, you can
/// create something that is not an l-value.   For example if your
/// l-value is "a[i]" then substituting i for a constant results in an
/// l-value but substituting a for a constant (array) wouldn't.  This
/// only applies to the "top level" of the expression, for example, it
/// is OK to replace b with a constant array in a[b[0]].
class address_of_aware_replace_symbolt : public unchecked_replace_symbolt
{
public:
  bool replace(exprt &dest) const override;

private:
  mutable bool require_lvalue = false;

  class set_require_lvalue_and_backupt
  {
  public:
    set_require_lvalue_and_backupt(bool &require_lvalue, const bool value)
      : require_lvalue(require_lvalue), prev_value(require_lvalue)
    {
      require_lvalue = value;
    }

    ~set_require_lvalue_and_backupt()
    {
      require_lvalue = prev_value;
    }

  private:
    bool &require_lvalue;
    bool prev_value;
  };

  bool replace_symbol_expr(symbol_exprt &dest) const override;
};

#endif // CPROVER_UTIL_REPLACE_SYMBOL_H
