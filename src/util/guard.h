/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GUARD_H
#define CPROVER_GUARD_H

#include <iosfwd>

#include "expr.h"

class guardt:public exprt
{
public:
  guardt()
  {
    make_true();
  }

  guardt& operator=(const exprt &e)
  {
    *this=static_cast<const guardt&>(e);

    return *this;
  }

  void add(const exprt &expr);

  void append(const guardt &guard)
  {
    add(guard);
  }

  //exprt as_expr(guard_listt::const_iterator it) const;

  exprt as_expr() const
  {
    return *this;
  }
  
  void guard_expr(exprt &dest) const;

#if 0
  bool empty() const { return guard_list.empty(); }
  bool is_true() const { return empty(); } 
  bool is_false() const;
  
  void make_true()
  {
    guard_list.clear();
  }
  
  void make_false();
#endif
  
  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);
  
#if 0
  void swap(guardt &g)
  {
    guard_list.swap(g.guard_list);
  }

  friend std::ostream &operator << (std::ostream &out, const guardt &g);
  
  size_type size() const
  {
    return guard_list.size();
  }
  
  void resize(size_type s)
  {
    guard_list.resize(s);
  }
  
  const guard_listt &get_guard_list() const
  {
    return guard_list;
  }

protected:
  guard_listt guard_list;  
#endif
};

#if 0
#define Forall_guard(it, guard_list) \
  for(guardt::guard_listt::iterator it=(guard_list).begin(); \
      it!=(guard_list).end(); ++it)

#define forall_guard(it, guard_list) \
  for(guardt::guard_listt::const_iterator it=(guard_list).begin(); \
      it!=(guard_list).end(); ++it)
#endif

#endif
