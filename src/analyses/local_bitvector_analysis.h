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

    // the bits for the "bitvector analysis"
    typedef enum
    {
      B_unknown=1<<0,
      B_uninitialized=1<<1,
      B_uses_offset=1<<2,
      B_dynamic_local=1<<3,
      B_dynamic_heap=1<<4,
      B_null=1<<5,
      B_static_lifetime=1<<6,
      B_integer_address=1<<7
    } bitst;

    explicit inline flagst(const bitst _bits):bits(_bits)
    {
    }
      
    unsigned bits;
    
    inline bool merge(const flagst &other)
    {
      unsigned old=bits;
      bits|=other.bits; // bit-wise or
      return old!=bits;
    }
    
    inline static flagst mk_unknown()
    {
      return flagst(B_unknown);
    }

    inline bool is_unknown() const
    {
      return (bits&B_unknown)!=0;
    }

    inline static flagst mk_uninitialized()
    {
      return flagst(B_uninitialized);
    }

    inline bool is_uninitialized() const
    {
      return (bits&B_uninitialized)!=0;
    }

    inline static flagst mk_uses_offset()
    {
      return flagst(B_uses_offset);
    }

    inline bool is_uses_offset() const
    {
      return (bits&B_uses_offset)!=0;
    }

    inline static flagst mk_dynamic_local()
    {
      return flagst(B_dynamic_local);
    }

    inline bool is_dynamic_local() const
    {
      return (bits&B_dynamic_local)!=0;
    }

    inline static flagst mk_dynamic_heap()
    {
      return flagst(B_dynamic_heap);
    }

    inline bool is_dynamic_heap() const
    {
      return (bits&B_dynamic_heap)!=0;
    }

    inline static flagst mk_null()
    {
      return flagst(B_null);
    }

    inline bool is_null() const
    {
      return (bits&B_null)!=0;
    }

    inline static flagst mk_static_lifetime()
    {
      return flagst(B_static_lifetime);
    }

    inline bool is_static_lifetime() const
    {
      return (bits&B_static_lifetime)!=0;
    }

    inline static flagst mk_integer_address()
    {
      return flagst(B_integer_address);
    }

    inline bool is_integer_address() const
    {
      return (bits&B_integer_address)!=0;
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
