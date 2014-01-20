/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_BITVECTOR_ANALYSIS_H
#define CPROVER_LOCAL_BITVECTOR_ANALYSIS_H

#include <stack>

#include <util/expanding_vector.h>

#include "locals.h"
#include "dirty.h"
#include "local_cfg.h"

/*******************************************************************\

   Class: local_may_aliast
   
 Purpose:

\*******************************************************************/

class local_bitvector_analysist
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  
  explicit local_bitvector_analysist(
    const goto_functiont &_goto_function):
    dirty(_goto_function),
    locals(_goto_function),
    cfg(_goto_function.body)
  {
    build(_goto_function);
  }

  void output(
    std::ostream &out,
    const goto_functiont &goto_function,
    const namespacet &ns) const;
  
  dirtyt dirty;
  localst locals;
  local_cfgt cfg;

  // categories of things one can point to
  struct flagst
  {
    inline flagst():bits(0)
    {
    }
    
    void clear()
    {
      bits=0;
    }

    union
    {
      // the bits for the "bitvector analysis"
      struct
      {
        bool unknown:1;
        bool uninitialized:1;
        bool uses_offset:1;
        bool dynamic_local:1;
        bool dynamic_heap:1;
        bool null:1;
        bool static_lifetime:1;
        bool integer_address:1;
      };
      
      unsigned bits;
    };
    
    inline bool merge(const flagst &other)
    {
      unsigned old=bits;
      bits|=other.bits; // bit-wise or
      return old!=bits;
    }
    
    inline static flagst mk_unknown()
    {
      flagst result;
      result.unknown=true;
      return result;
    }

    inline static flagst mk_uninitialized()
    {
      flagst result;
      result.uninitialized=true;
      return result;
    }

    inline static flagst mk_uses_offset()
    {
      flagst result;
      result.uses_offset=true;
      return result;
    }

    inline static flagst mk_dynamic_local()
    {
      flagst result;
      result.dynamic_local=true;
      return result;
    }

    inline static flagst mk_dynamic_heap()
    {
      flagst result;
      result.dynamic_heap=true;
      return result;
    }

    inline static flagst mk_null()
    {
      flagst result;
      result.null=true;
      return result;
    }

    inline static flagst mk_static_lifetime()
    {
      flagst result;
      result.static_lifetime=true;
      return result;
    }

    inline static flagst mk_integer_address()
    {
      flagst result;
      result.integer_address=true;
      return result;
    }

    void print(std::ostream &) const;
  };

  friend std::ostream & operator << (std::ostream &out, const flagst f)
  {
    f.print(out);
    return out;
  }
  
  inline friend flagst operator|(const flagst f1, const flagst f2)
  {
    flagst result=f1;
    result.bits|=f2.bits;
    return result;
  }

  flagst get(
    const goto_programt::const_targett t,
    const exprt &src);
  
protected:
  void build(const goto_functiont &goto_function);

  typedef std::stack<unsigned> work_queuet;

  numbering<irep_idt> pointers;
  
  // pointers -> flagst
  // This is a vector, so it's fast.
  typedef expanding_vector<flagst> points_tot;

  // the information tracked per program location  
  class loc_infot
  {
  public:
    points_tot points_to;
    
    bool merge(const loc_infot &src);
  };

  typedef std::vector<loc_infot> loc_infost;
  loc_infost loc_infos;
  
  void assign_lhs(
    const exprt &lhs,
    const exprt &rhs,
    const loc_infot &loc_info_src,
    loc_infot &loc_info_dest);
    
  flagst get_rec(
    const exprt &rhs,
    const loc_infot &loc_info_src);
    
  bool is_tracked(const irep_idt &identifier);
};

#endif
