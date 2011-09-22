/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_RW_SET
#define CPROVER_GOTO_PROGRAMS_RW_SET

#include <hash_cont.h>
#include <guard.h>
#include <std_code.h>
#include <namespace.h>
#include <expr_util.h>

#include <pointer-analysis/value_sets.h>

class rw_sett
{
public:
  struct entryt
  {
    irep_idt object;
    bool r, w;
    exprt guard;
    
    entryt():r(false), w(false),
             guard(true_exprt())
    {
    }
    
    const exprt &get_guard() const
    {
      return guard;
    }
    
    std::string get_comment() const
    {
      std::string result;
      if(w)
        result="W/W";
      else
        result="R/W";
        
      result+=" data race on ";
      result+=id2string(object);
      return result;
    }
  };
  
  typedef hash_map_cont<irep_idt, entryt, irep_id_hash> entriest;
  entriest entries;
  
  void compute(const codet &code);
  
  rw_sett(const namespacet &_ns,
          value_setst &_value_sets,
          goto_programt::const_targett _target):
          ns(_ns),
          value_sets(_value_sets),
          target(_target)
  {
  }
  
  rw_sett(const namespacet &_ns,
          value_setst &_value_sets,
          goto_programt::const_targett _target,
          const codet &code):ns(_ns),
          value_sets(_value_sets),
          target(_target)
  {
    compute(code);
  }
  
  void read(const exprt &expr)
  {
    read_write_rec(expr, true, false, "", guardt());
  }
  
  void read(const exprt &expr, const guardt &guard)
  {
    read_write_rec(expr, true, false, "", guard);
  }
  
protected:
  const namespacet &ns;
  value_setst &value_sets;
  const goto_programt::const_targett target;

  void assign(const exprt &lhs, const exprt &rhs);

  void read_write_rec(
    const exprt &expr,
    bool r, bool w,
    const std::string &suffix,
    const guardt &guard);
};

#define forall_rw_set_entries(it, rw_set) \
  for(rw_sett::entriest::const_iterator it=(rw_set).entries.begin(); \
      it!=(rw_set).entries.end(); it++)

#endif
