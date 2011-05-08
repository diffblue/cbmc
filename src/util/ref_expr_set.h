/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_REF_EXPR_SET_H
#define CPROVER_UTIL_REF_EXPR_SET_H

#include <set>

#include <hash_cont.h>
#include <expr.h>
#include <reference_counting.h>

extern const hash_set_cont<exprt, irep_hash> empty_expr_set;

struct ref_expr_set_dt
{
  typedef hash_set_cont<exprt, irep_hash> expr_sett;
  expr_sett expr_set;
  
  const static ref_expr_set_dt empty;
};

class ref_expr_sett:public reference_counting<ref_expr_set_dt>
{
public:
  typedef ref_expr_set_dt::expr_sett expr_sett;

  bool empty() const
  {
    if(d==NULL) return true;
    return d->expr_set.empty();
  }

  inline const expr_sett &expr_set() const
  {
    return read().expr_set;
  }
  
  inline expr_sett &expr_set_write()
  {
    return write().expr_set;
  }
  
  bool make_union(const ref_expr_sett &s2)
  {
    if(s2.d==NULL) return false;
    
    if(s2.d==d) return false;
  
    if(d==NULL)
    {
      copy_from(s2);
      return true;
    }

    return make_union(s2.d->expr_set);
  }

  bool make_union(const expr_sett &s2)
  {
    expr_sett tmp(read().expr_set);
    unsigned old_size=tmp.size();
    tmp.insert(s2.begin(), s2.end());
    
    // anything new?
    if(tmp.size()==old_size) return false;
    move(tmp);
    return true;
  }

  void move(expr_sett &s2)
  {
    clear();
    write().expr_set.swap(s2);
  }
};

#endif
