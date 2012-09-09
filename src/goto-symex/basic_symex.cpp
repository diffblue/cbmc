/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <base_type.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <cprover_prefix.h>
#include <expr_util.h>
#include <std_expr.h>
#include <context.h>
#include <guard.h>

#include <ansi-c/c_types.h>

#include "basic_symex.h"
#include "goto_symex_state.h"

unsigned basic_symext::nondet_count=0;
unsigned basic_symext::dynamic_counter=0;

/*******************************************************************\

Function: basic_symext::do_simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::do_simplify(exprt &expr)
{
  if(options.get_bool_option("simplify"))
    simplify(expr, ns);
}

/*******************************************************************\

Function: basic_symext::symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex(statet &state, const codet &code)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_block)
    symex_block(state, code);
  else if(statement==ID_assign)
    symex_assign(state, to_code_assign(code)); /* TODO: expression must be clean */
  else if(statement==ID_decl)
  {
    // behaves like non-deterministic assignment
    if(code.operands().size()!=1)
      throw "decl expected to have one operand";

    exprt rhs(ID_nondet_symbol, code.op0().type());
    rhs.set(ID_identifier, "symex::nondet"+i2string(nondet_count++));
    rhs.location()=code.location();

    exprt new_lhs=code.op0();
    read(new_lhs);

    guardt guard; // NOT the state guard!
    symex_assign_rec(state, new_lhs, nil_exprt(), rhs, guard, VISIBLE);
  }
  else if(statement==ID_expression)
  {
    // ignore
  }
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
    symex_cpp_delete(state, code);
  else if(statement==ID_free)
  {
    // like skip
  }
  else if(statement==ID_nondet)
  {
    // like skip
  }
  else if(statement==ID_printf)
    symex_printf(state, static_cast<const exprt &>(get_nil_irep()), code);
  else if(statement==ID_asm)
  {
    // ignore for now
  }
  else
  {
    std::cerr << code.pretty() << std::endl;
    throw "unexpected statement: "+id2string(statement);
  }
}

/*******************************************************************\

Function: basic_symext::symex_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_block(statet &state, const codet &code)
{
  forall_operands(it, code)
    symex(state, to_code(*it));
}

/*******************************************************************\

Function: basic_symext::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::read(exprt &expr)
{
}

/*******************************************************************\

Function: basic_symext::replace_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::replace_nondet(exprt &expr)
{
  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_nondet)
  {
    exprt new_expr(ID_nondet_symbol, expr.type());
    new_expr.set(ID_identifier, "symex::nondet"+i2string(nondet_count++));
    new_expr.location()=expr.location();
    expr.swap(new_expr);
  }
  else
    Forall_operands(it, expr)
      replace_nondet(*it);
}
