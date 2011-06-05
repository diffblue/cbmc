/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BASIC_SYMEX_H
#define CPROVER_BASIC_SYMEX_H

#include <map>
#include <set>

#include <options.h>
#include <namespace.h>
#include <replace_expr.h>
#include <std_code.h>
#include <std_expr.h>

#include "symex_target.h"
#include "goto_symex_state.h"

class basic_symext
{
public:
  basic_symext(
    const namespacet &_ns,
    contextt &_new_context,
    symex_targett &_target):
    constant_propagation(true),
    new_context(_new_context),
    ns(_ns),
    target(_target)
  {
    options.set_option("simplify", true);
  }

  virtual ~basic_symext() { }

  typedef goto_symex_statet statet;

  virtual void symex(statet &state, const codet &code);
  bool constant_propagation;

  optionst options;
  contextt &new_context;

protected:
  const namespacet &ns;
  symex_targett &target;
  
  virtual void do_simplify(exprt &expr);
  
  virtual void symex_block(statet &state, const codet &code);
  virtual void symex_assign(statet &state, const code_assignt &code);
  
  typedef enum { VISIBLE, HIDDEN } visibilityt;
  
  void symex_assign_rec(statet &state, const exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_symbol(statet &state, const symbol_exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_typecast(statet &state, const typecast_exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_array(statet &state, const index_exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_member(statet &state, const member_exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_if(statet &state, const if_exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  void symex_assign_byte_extract(statet &state, const exprt &lhs, const exprt &rhs, guardt &guard, visibilityt visibility);
  
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
};

void basic_symex(
  const codet &code,
  const namespacet &ns,
  symex_targett &target,
  goto_symex_statet &state);

void basic_symex(
  const codet &code,
  const namespacet &ns,
  symex_targett &target);

#endif
