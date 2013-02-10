/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_H

/*! \defgroup goto_symex Symbolic execution of goto programs
*/

#include <options.h>

#include <goto-programs/goto_functions.h>

#include "goto_symex_state.h"

class typet;
class code_typet;
class symbol_tablet;
class code_assignt;
class code_function_callt;
class exprt;
class goto_symex_statet;
class guardt;
class if_exprt;
class index_exprt;
class symbol_exprt;
class member_exprt;
class namespacet;
class side_effect_exprt;
class symex_targett;
class typecast_exprt;

/*! \brief The main class for the forward symbolic simulator
*/
class goto_symext
{
public:
  goto_symext(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target):
    total_claims(0),
    remaining_claims(0),
    constant_propagation(true),
    new_symbol_table(_new_symbol_table),
    ns(_ns),
    target(_target),
    guard_identifier("goto_symex::\\guard")
  {
    options.set_option("simplify", true);
    options.set_option("assertions", true);
  }
  
  virtual ~goto_symext()
  {
  }

  typedef goto_symex_statet statet;

  /** symex all at once, starting from entry point */
  virtual void operator()(
    const goto_functionst &goto_functions);

  /** symex starting from given goto program */
  virtual void operator()(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program);

  /** start symex in a given state */
  virtual void operator()(
    statet &state,
    const goto_functionst &goto_functions,
    const goto_programt &goto_program);	   

  /** execute just one step */
  virtual void symex_step(
    const goto_functionst &goto_functions,
    statet &state);

  // these bypass the target maps
  virtual void symex_step_return(statet &state);
  virtual void symex_step_goto(statet &state, bool taken);
  
  // statistics
  unsigned total_claims, remaining_claims;

  bool constant_propagation;

  optionst options;
  symbol_tablet &new_symbol_table;

protected:
  const namespacet &ns;
  symex_targett &target;  

  friend class symex_dereference_statet;
  
  void new_name(symbolt &symbol);
  
  // this does the following:
  // a) rename non-det choices
  // b) remove pointer dereferencing
  // c) rewrite array_equal expression into equality
  void clean_expr(
    exprt &expr, statet &state, bool write);
    
  void replace_array_equal(exprt &expr);
  void adjust_float_expressions(exprt &expr);
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
  virtual void symex_start_thread(statet &state);
  virtual void symex_atomic_begin(statet &state);
  virtual void symex_atomic_end(statet &state);  
  virtual void symex_decl(statet &state);
  virtual void symex_return(statet &state);

  virtual void symex_other(
    const goto_functionst &goto_functions,
    statet &state);    
    
  virtual void claim(
    const exprt &expr,
    const std::string &msg,
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
    const irep_idt function_identifier,
    const code_typet &function_type,
    statet &state,
    const exprt::operandst &arguments);

  void locality(
    const irep_idt function_identifier,
    statet &state,
    const goto_functionst::goto_functiont &goto_function);

  void add_end_of_function(
    exprt &code,
    const irep_idt &identifier);
                           
  std::map<irep_idt, unsigned> function_unwind;
  std::map<symex_targett::sourcet, unsigned> unwind_map;
  
  // exceptions
  
  void symex_throw(statet &state);
  void symex_catch(statet &state);

  virtual void do_simplify(exprt &expr);
  
  //virtual void symex_block(statet &state, const codet &code);
  virtual void symex_assign(statet &state, const code_assignt &code);
  
  typedef enum { VISIBLE, HIDDEN } visibilityt;
  
  void symex_assign_rec(statet &state, const exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_symbol(statet &state, const symbol_exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_typecast(statet &state, const typecast_exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_array(statet &state, const index_exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_member(statet &state, const member_exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_if(statet &state, const if_exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_byte_extract(statet &state, const exprt &lhs, const exprt &full_lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  
  static exprt add_to_lhs(const exprt &lhs, const exprt &what);
  
  virtual void symex_gcc_builtin_va_arg_next(statet &state, const exprt &lhs, const side_effect_exprt &code);
  virtual void symex_malloc        (statet &state, const exprt &lhs, const side_effect_exprt &code);
  virtual void symex_cpp_delete    (statet &state, const codet &code);
  virtual void symex_cpp_new       (statet &state, const exprt &lhs, const side_effect_exprt &code);
  virtual void symex_fkt           (statet &state, const code_function_callt &code);
  virtual void symex_macro         (statet &state, const code_function_callt &code);
  virtual void symex_trace         (statet &state, const code_function_callt &code);
  virtual void symex_printf        (statet &state, const exprt &lhs, const exprt &rhs);
  virtual void symex_input         (statet &state, const codet &code);
  virtual void symex_output        (statet &state, const codet &code);

  static unsigned nondet_count;
  static unsigned dynamic_counter;
  
  void read(exprt &expr);
  void replace_nondet(exprt &expr);
  void rewrite_quantifiers(exprt &expr, statet &state);
};

#endif
