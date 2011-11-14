/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

/*! \defgroup goto_symex Symbolic execution of goto programs
*/

#include <std_types.h>
#include <goto-programs/goto_functions.h>

#include "basic_symex.h"

class goto_symext:
  public basic_symext
{
public:
  goto_symext(
    const namespacet &_ns,
    contextt &_new_context,
    symex_targett &_target):
    basic_symext(_ns, _new_context, _target),
    total_claims(0),
    remaining_claims(0),
    guard_identifier("goto_symex::\\guard")
  {
    options.set_option("assertions", true);
  }

  // all at once
  virtual void operator()(
    const goto_functionst &goto_functions);

  virtual void operator()(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program);

  // start in a given state
  virtual void operator()(
    statet &state,
    const goto_functionst &goto_functions,
    const goto_programt &goto_program);	   

  // execute one step
  virtual void symex_step(
    const goto_functionst &goto_functions,
    statet &state);

  // these bypass the target maps
  virtual void symex_step_return(statet &state);
  virtual void symex_step_goto(statet &state, bool taken);
  
  // statistics
  unsigned total_claims, remaining_claims;

protected:
  friend class symex_dereference_statet;
  
  void new_name(symbolt &symbol);
  
  // this does the following:
  // a) rename non-det choices
  // b) remove pointer dereferencing
  // c) rewrite array_equal expression into equality
  void clean_expr(
    exprt &expr, statet &state, bool write);
    
  void replace_array_equal(exprt &expr);
  void trigger_auto_object(const exprt &expr, statet &state);
  void initialize_auto_object(const exprt &expr, statet &state);
  void process_array_expr(exprt &expr);
  exprt make_auto_object(const typet &type);

  virtual void dereference(
    exprt &expr,
    statet &state,
    const bool write);
  
  void dereference_rec(
    exprt &expr,
    statet &state,
    guardt &guard,
    const bool write);
  
  void dereference_rec_address_of(
    exprt &expr,
    statet &state,
    guardt &guard);
    
  static bool is_index_member_symbol_if(const exprt &expr);
  
  exprt address_arithmetic(
    const exprt &expr,
    statet &state,
    guardt &guard);
  
  // guards
  
  irep_idt guard_identifier;
  
  // symex

  virtual void symex_goto(statet &state);
  virtual void symex_decl(statet &state);
  virtual void symex_return(statet &state);

  virtual void symex_other(
    const goto_functionst &goto_functions,
    statet &state);    
    
  virtual void claim(
    const exprt &expr,
    const std::string &msg,
    unsigned priority,
    statet &state);
    
  // gotos
  void merge_gotos(statet &state);
  
  void merge_value_sets(
    const statet::goto_statet &goto_state,
    statet &dest);
      
  void phi_function(
    const statet::goto_statet &goto_state,
    statet &state);
  
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);
  
  virtual void loop_bound_exceeded(statet &state, const exprt &guard);
  
  // function calls
  
  void pop_frame(statet &state);
  void return_assignment(statet &state);
  
  virtual void no_body(const irep_idt &identifier)
  {
  }

  virtual void symex_function_call(
    const goto_functionst &goto_functions,
    statet &state,
    const code_function_callt &call);

  virtual void symex_end_of_function(statet &state);

  virtual void symex_function_call_symbol(
    const goto_functionst &goto_functions,
    statet &state,
    const code_function_callt &call);

  virtual void symex_function_call_code(
    const goto_functionst &goto_functions,
    statet &state,
    const code_function_callt &call);
    
  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    unsigned unwind);

  void argument_assignments(
    const code_typet &function_type,
    statet &state,
    const exprt::operandst &arguments);

  void locality(
    unsigned frame_counter,
    statet &state,
    const goto_functionst::goto_functiont &goto_function);

  void add_end_of_function(
    exprt &code,
    const irep_idt &identifier);
                           
  std::map<irep_idt, unsigned> function_unwind;
  std::map<irep_idt, unsigned> function_frame;
  std::map<symex_targett::sourcet, unsigned> unwind_map;
};

#endif
