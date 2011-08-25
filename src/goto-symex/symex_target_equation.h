/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BASIC_SYMEX_EQUATION_H
#define CPROVER_BASIC_SYMEX_EQUATION_H

#include <list>
#include <map>

#include <namespace.h>

#include <goto-programs/goto_program.h>
#include <solvers/prop/prop_conv.h>

#include "symex_target.h"
#include "goto_trace.h"

class symex_target_equationt:public symex_targett
{
public:
  symex_target_equationt(const namespacet &_ns):ns(_ns) { }

  // assignment to a variable - lhs must be symbol
  virtual void assignment(
    const guardt &guard,
    const symbol_exprt &ssa_lhs,
    const symbol_exprt &original_lhs,
    const exprt &full_lhs,
    const exprt &ssa_rhs,
    const sourcet &source,
    assignment_typet assignment_type);
    
  // just record a location
  virtual void location(
    const guardt &guard,
    const sourcet &source);
  
  // output
  virtual void output(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &fmt,
    const std::list<exprt> &args);
  
  // output, formatted
  virtual void output_fmt(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &output_id,
    const irep_idt &fmt,
    const std::list<exprt> &args);
  
  // input
  virtual void input(
    const guardt &guard,
    const sourcet &source,
    const irep_idt &input_id,
    const std::list<exprt> &args);
  
  // record an assumption
  virtual void assumption(
    const guardt &guard,
    const exprt &cond,
    const sourcet &source);

  // record an assertion
  virtual void assertion(
    const guardt &guard,
    const exprt &cond,
    const std::string &msg,
    const sourcet &source);

  void convert(prop_convt &prop_conv);
  void convert_assignments(decision_proceduret &decision_procedure) const;
  void convert_assumptions(prop_convt &prop_conv);
  void convert_assertions(prop_convt &prop_conv);
  void convert_guards(prop_convt &prop_conv);
  void convert_io(decision_proceduret &decision_procedure);

  exprt make_expression() const;

  class SSA_stept
  {
  public:
    sourcet source;
    goto_trace_stept::typet type;
    
    bool is_assert() const     { return type==goto_trace_stept::ASSERT; }
    bool is_assume() const     { return type==goto_trace_stept::ASSUME; }
    bool is_assignment() const { return type==goto_trace_stept::ASSIGNMENT; }
    bool is_location() const   { return type==goto_trace_stept::LOCATION; }
    bool is_output() const     { return type==goto_trace_stept::OUTPUT; }
    
    exprt guard_expr;
    literalt guard_literal;

    // for ASSIGNMENT  
    symbol_exprt ssa_lhs, original_lhs_object;
    exprt full_lhs;
    exprt ssa_rhs;
    assignment_typet assignment_type;
    
    // for ASSUME/ASSERT
    exprt cond_expr; 
    literalt cond_literal;
    std::string comment;

    // for INPUT/OUTPUT
    irep_idt format_string, io_id;
    bool formatted;
    std::list<exprt> io_args;
    std::list<exprt> converted_io_args;
    
    // for slicing
    bool ignore;
    
    SSA_stept():
      guard_expr(static_cast<const exprt &>(get_nil_irep())),
      ssa_lhs(static_cast<const symbol_exprt &>(get_nil_irep())),
      original_lhs_object(static_cast<const symbol_exprt &>(get_nil_irep())),
      full_lhs(static_cast<const exprt &>(get_nil_irep())),
      ssa_rhs(static_cast<const exprt &>(get_nil_irep())),
      cond_expr(static_cast<const exprt &>(get_nil_irep())),
      formatted(false),
      ignore(false)
    {
    }
    
    void output(
      const namespacet &ns,
      std::ostream &out) const;
  };
  
  unsigned count_assertions() const
  {
    unsigned i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->is_assert()) i++;
    return i;
  }
  
  unsigned count_ignored_SSA_steps() const
  {
    unsigned i=0;
    for(SSA_stepst::const_iterator
        it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->ignore) i++;
    return i;
  }

  typedef std::list<SSA_stept> SSA_stepst;
  SSA_stepst SSA_steps;
  
  SSA_stepst::iterator get_SSA_step(unsigned s)
  {
    SSA_stepst::iterator it=SSA_steps.begin();
    for(; s!=0; s--)
    {
      assert(it!=SSA_steps.end());
      it++;
    }
    return it;
  }

  void output(std::ostream &out) const;
  
  void clear()
  {
    SSA_steps.clear();
  }
  
protected:
  const namespacet &ns;
};

extern inline bool operator<(
  const symex_target_equationt::SSA_stepst::const_iterator a,
  const symex_target_equationt::SSA_stepst::const_iterator b)
{
  return &(*a)<&(*b);
}

std::ostream &operator<<(std::ostream &out, const symex_target_equationt::SSA_stept &step);
std::ostream &operator<<(std::ostream &out, const symex_target_equationt &equation);

#endif
