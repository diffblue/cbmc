/*******************************************************************

 Module: Remove ternaries by rewritting into IFs.

 Author: Daniel Neville.
         John Galea.

 Date:   September 2016

 \*******************************************************************/

#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <util/i2string.h>
#include <util/replace_expr.h>
#include <iostream>

#include "remove_ternary.h"

class remove_ternaryt
{
public:
  explicit remove_ternaryt(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;

  unsigned int replaced = 0;

  void replace_ternary(
      goto_programt &goto_program,
      goto_programt::instructionst::iterator &i_it,
          exprt &expr,
          bool lhs);
};


/*******************************************************************
 Function:  Replace ternary

 Inputs:  Takes:
 - A Goto Program, used to insert new instructions.
 - A specific instruction, used to know the current location
 in the program.  This is handled using pointer introduction.
 - Ternaries on the LHS are generally of poor readability and
 are avoided by many developers.
 - The current expr, analysed recursively.

 Outputs:  Modified instruction.

 Purpose:

 \*******************************************************************/

void remove_ternaryt::replace_ternary(goto_programt &goto_program,
    goto_programt::instructionst::iterator &i_it, exprt &expr, bool lhs)
{
  // Ternary must have operands by definition.
  if(!expr.has_operands())
    return;

  /* LHS handles ternary when used on the LHS of an assignment
   * operator.
   * LHS = false is used whenever the ternary is simply
   * part of an arbitrary condition (including all RHS)
   */

  if(expr.id() == ID_code)
  {
    codet &code=to_code(expr);
    if(code.get_statement() == ID_assign)
    {
      code_assignt &code_assign=to_code_assign(code);

      replace_ternary(goto_program, i_it, code_assign.lhs(), true);
      replace_ternary(goto_program, i_it, code_assign.rhs(), false);

      return;
    }
  }

  Forall_operands(it, expr)
  {
    // Go through sub-tree first.
    // This allows parsing the expr-tree leaf first.
    replace_ternary(goto_program, i_it, *it, lhs);
  }

  // If we are on an IF statement.
  if(expr.id() == ID_if)
  {
    if_exprt &if_expr=to_if_expr(expr); // Some short hands.

    /* 1  (...) cond : T : F (...)
     -> (where x is some integer)
     1  decl tmp_x;
     2  if !cond GOTO false_case_x
     3  tmp_x = T
     4  GOTO end_x
     6  false_case_x:  tmp_x = F
     7  end_x: (...) tmp_x (...) // replace ternary with tmp_x
     */

    auxiliary_symbolt new_symbol;
    symbolt *symbol_ptr;

    do
    {
      new_symbol.base_name="tmp_ternary$" + i2string(++replaced);
      new_symbol.name="ternary" + id2string(new_symbol.base_name);
      new_symbol.type=if_expr.true_case().type();
      if(lhs)
        new_symbol.type=pointer_typet(new_symbol.type);
      new_symbol.location=i_it->source_location;
    } while (symbol_table.move(new_symbol, symbol_ptr));

    goto_programt::targett decl_instruction=goto_program.insert_before(i_it);
    goto_programt::targett guarded_goto_instruction=goto_program.insert_before(
        i_it);
    goto_programt::targett true_instruction=goto_program.insert_before(i_it);
    goto_programt::targett unguarded_goto_instruction=
        goto_program.insert_before(i_it);
    goto_programt::targett false_instruction=goto_program.insert_before(i_it);

    code_declt decl;
    decl.symbol()=symbol_ptr->symbol_expr();
    decl.add_source_location()=i_it->source_location;
    decl_instruction->make_decl();
    decl_instruction->code=decl;

    code_gotot guarded_goto;
    guarded_goto_instruction->make_goto();
    guarded_goto_instruction->code=guarded_goto;
    guarded_goto_instruction->guard=not_exprt(if_expr.cond());
    guarded_goto_instruction->targets.push_back(false_instruction);

    code_assignt assign_true;
    assign_true.lhs()=symbol_ptr->symbol_expr();
    assign_true.rhs()=if_expr.true_case();
    assign_true.add_source_location()=i_it->source_location;
    true_instruction->make_assignment();

    code_gotot unguarded_goto;
    unguarded_goto_instruction->make_goto();
    unguarded_goto_instruction->code=unguarded_goto;
    unguarded_goto_instruction->guard=true_exprt();
    unguarded_goto_instruction->targets.push_back(i_it);

    code_assignt assign_false;
    assign_false.lhs()=symbol_ptr->symbol_expr();
    assign_false.rhs()=if_expr.false_case();
    assign_false.add_source_location()=i_it->source_location;
    false_instruction->make_assignment();
    false_instruction->code=assign_false;

    expr=symbol_ptr->symbol_expr();

    if(lhs)
    {
      expr=dereference_exprt(expr);
      assign_true.rhs()=address_of_exprt(assign_true.rhs());
      assign_false.rhs()=address_of_exprt(assign_false.rhs());
    }

    true_instruction->code=assign_true;
    false_instruction->code=assign_false;
  }
}

/*******************************************************************
 Function: remove_ternaryt::operator()(goto_functionst &goto_functions)

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void remove_ternaryt::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions) {
    goto_programt &goto_program=f_it->second.body;

    Forall_goto_program_instructions(i_it, goto_program)
    replace_ternary(goto_program, i_it, i_it->code, false);
  }

  goto_functions.update();
}

/*******************************************************************
 Function: remove_ternary(symbol_tablet &symbol_table,
 goto_functionst &goto_functions)

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void remove_ternary(symbol_tablet &symbol_table,
    goto_functionst &goto_functions)
{
  remove_ternaryt rt(symbol_table);
  rt(goto_functions);
}

/*******************************************************************
 Function: remove_ternary(goto_modelt &goto_model)

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void remove_ternary(goto_modelt &goto_model)
{
  remove_ternaryt rt(goto_model.symbol_table);
  rt(goto_model.goto_functions);
}

