/*******************************************************************\

Module: Object Identifiers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_OBJECT_ID_H
#define CPROVER_OBJECT_ID_H

#include <set>
#include <iostream>

#include <std_expr.h>
#include <std_code.h>

class object_idt
{
public:
  object_idt() { }

  explicit object_idt(const symbol_exprt &symbol_expr)
  {
    id=symbol_expr.get_identifier();
  }
  
  friend std::ostream &operator << (std::ostream &out, const object_idt &x)
  {
    return out << x.id;
  }

  friend inline bool operator < (const object_idt &a, const object_idt &b)
  {
    return a.id < b.id;
  }
  
protected:
  irep_idt id;
};

inline std::ostream &operator << (std::ostream &, const object_idt &);
inline bool operator < (const object_idt &a, const object_idt &b);

typedef std::set<object_idt> object_id_sett;

void get_objects(const exprt &expr, object_id_sett &dest);
void get_objects_r(const code_assignt &assign, object_id_sett &);
void get_objects_w(const code_assignt &assign, object_id_sett &);

#endif
