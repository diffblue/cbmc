/*******************************************************************\

Module: Object Identifiers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Object Identifiers

#ifndef CPROVER_GOTO_INSTRUMENT_OBJECT_ID_H
#define CPROVER_GOTO_INSTRUMENT_OBJECT_ID_H

#include <iosfwd>
#include <set>

#include <util/std_expr.h>

class code_assignt;

class object_idt
{
public:
  object_idt() { }

  explicit object_idt(const symbol_exprt &symbol_expr)
  {
    id=symbol_expr.get_identifier();
  }

  explicit object_idt(const irep_idt &identifier)
  {
    id=identifier;
  }

  bool operator<(const object_idt &other) const
  {
    return id<other.id;
  }

  const irep_idt &get_id() const
  {
    return id;
  }

protected:
  irep_idt id;
};

inline std::ostream &operator<<(
  std::ostream &out,
  const object_idt &object_id)
{
  return out << object_id.get_id();
}

typedef std::set<object_idt> object_id_sett;

void get_objects(const exprt &expr, object_id_sett &dest);
void get_objects_r(const code_assignt &assign, object_id_sett &);
void get_objects_w(const code_assignt &assign, object_id_sett &);
void get_objects_w_lhs(const exprt &lhs, object_id_sett &);
void get_objects_r_lhs(const exprt &lhs, object_id_sett &);

#endif // CPROVER_GOTO_INSTRUMENT_OBJECT_ID_H
