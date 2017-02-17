/*******************************************************************\

Module: Remove function return values

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "remove_returns.h"

class remove_returnst
{
public:
  explicit remove_returnst(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

  void restore(
    goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;

  void replace_returns(
    goto_functionst::function_mapt::iterator f_it);

  void do_function_calls(
    goto_functionst &goto_functions,
    goto_programt &goto_program);

  bool restore_returns(
    goto_functionst::function_mapt::iterator f_it);

  void undo_function_calls(
    goto_functionst &goto_functions,
    goto_programt &goto_program);
};

/*******************************************************************\

Function: remove_returnst::replace_returns

Inputs:

Outputs:

Purpose: turns 'return x' into an assignment to fkt#return_value

\*******************************************************************/

void remove_returnst::replace_returns(
  goto_functionst::function_mapt::iterator f_it)
{
  typet return_type=f_it->second.type.return_type();

  const irep_idt function_id=f_it->first;

  // returns something but void?
  bool has_return_value=return_type!=empty_typet();

  if(has_return_value)
  {
    // look up the function symbol
    symbol_tablet::symbolst::iterator s_it=
      symbol_table.symbols.find(function_id);

    assert(s_it!=symbol_table.symbols.end());
    symbolt &function_symbol=s_it->second;

    // make the return type 'void'
    f_it->second.type.return_type()=empty_typet();
    function_symbol.type=f_it->second.type;

    // add return_value symbol to symbol_table
    auxiliary_symbolt new_symbol;
    new_symbol.is_static_lifetime=true;
    new_symbol.module=function_symbol.module;
    new_symbol.base_name=
      id2string(function_symbol.base_name)+RETURN_VALUE_SUFFIX;
    new_symbol.name=id2string(function_symbol.name)+RETURN_VALUE_SUFFIX;
    new_symbol.mode=function_symbol.mode;
    new_symbol.type=return_type;

    symbol_table.add(new_symbol);
  }

  goto_programt &goto_program=f_it->second.body;

  if(goto_program.empty())
    return;

  if(has_return_value)
  {
    Forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_return())
      {
        assert(i_it->code.operands().size()==1);

        // replace "return x;" by "fkt#return_value=x;"
        symbol_exprt lhs_expr;
        lhs_expr.set_identifier(id2string(function_id)+RETURN_VALUE_SUFFIX);
        lhs_expr.type()=return_type;

        code_assignt assignment(lhs_expr, i_it->code.op0());

        // now turn the `return' into `assignment'
        i_it->type=ASSIGN;
        i_it->code=assignment;
      }
    }
  }
}

/*******************************************************************\

Function: remove_returnst::do_function_calls

Inputs:

Outputs:

Purpose: turns x=f(...) into f(...); lhs=f#return_value;

\*******************************************************************/

void remove_returnst::do_function_calls(
  goto_functionst &goto_functions,
  goto_programt &goto_program)
{
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(i_it->code);

      code_typet old_type=to_code_type(function_call.function().type());

      // Do we return anything?
      if(old_type.return_type()!=empty_typet())
      {
        // replace "lhs=f(...)" by
        // "f(...); lhs=f#return_value; DEAD f#return_value;"
        assert(function_call.function().id()==ID_symbol);

        const irep_idt function_id=
          to_symbol_expr(function_call.function()).get_identifier();

        // see if we have a body
        goto_functionst::function_mapt::const_iterator
          f_it=goto_functions.function_map.find(function_id);

        if(f_it==goto_functions.function_map.end())
          throw
            "failed to find function `"+id2string(function_id)+
            "' in function map";

        // fix the type
        to_code_type(function_call.function().type()).return_type()=
          empty_typet();

        if(function_call.lhs().is_not_nil())
        {
          exprt rhs;

          if(f_it->second.body_available())
          {
            symbol_exprt return_value;
            return_value.type()=function_call.lhs().type();
            return_value.set_identifier(
              id2string(function_id)+RETURN_VALUE_SUFFIX);
            rhs=return_value;
          }
          else
          {
            rhs=side_effect_expr_nondett(function_call.lhs().type());
          }

          goto_programt::targett t_a=goto_program.insert_after(i_it);
          t_a->make_assignment();
          t_a->source_location=i_it->source_location;
          t_a->code=code_assignt(function_call.lhs(), rhs);
          t_a->function=i_it->function;

          // fry the previous assignment
          function_call.lhs().make_nil();

          if(f_it->second.body_available())
          {
            goto_programt::targett t_d=goto_program.insert_after(t_a);
            t_d->make_dead();
            t_d->source_location=i_it->source_location;
            t_d->code=code_deadt(rhs);
            t_d->function=i_it->function;
          }
        }
      }
    }
  }
}

/*******************************************************************\

Function: remove_returnst::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void remove_returnst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
  {
    replace_returns(it);
    do_function_calls(goto_functions, it->second.body);
  }
}

/*******************************************************************\

Function: remove_returns

Inputs:

Outputs:

Purpose: removes returns

\*******************************************************************/

void remove_returns(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_returnst rr(symbol_table);
  rr(goto_functions);
}

/*******************************************************************\

Function: remove_returns

Inputs:

Outputs:

Purpose: removes returns

\*******************************************************************/

void remove_returns(goto_modelt &goto_model)
{
  remove_returnst rr(goto_model.symbol_table);
  rr(goto_model.goto_functions);
}

/*******************************************************************\

Function: remove_returnst::restore_returns

Inputs:

Outputs:

Purpose: turns 'return x' into an assignment to fkt#return_value

\*******************************************************************/

bool remove_returnst::restore_returns(
  goto_functionst::function_mapt::iterator f_it)
{
  const irep_idt function_id=f_it->first;

  // do we have X#return_value?
  std::string rv_name=id2string(function_id)+RETURN_VALUE_SUFFIX;

  symbol_tablet::symbolst::iterator rv_it=
    symbol_table.symbols.find(rv_name);

  if(rv_it==symbol_table.symbols.end())
    return true;

  // look up the function symbol
  symbol_tablet::symbolst::iterator s_it=
    symbol_table.symbols.find(function_id);

  assert(s_it!=symbol_table.symbols.end());
  symbolt &function_symbol=s_it->second;

  // restore the return type
  f_it->second.type.return_type()=rv_it->second.type;
  function_symbol.type=f_it->second.type;

  // remove the return_value symbol from the symbol_table
  irep_idt rv_name_id=rv_it->second.name;
  symbol_table.symbols.erase(rv_it);

  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      code_assignt &assign=to_code_assign(i_it->code);
      if(assign.lhs().id()!=ID_symbol ||
         to_symbol_expr(assign.lhs()).get_identifier()!=rv_name_id)
        continue;

      // replace "fkt#return_value=x;" by "return x;"
      code_returnt return_code(assign.rhs());

      // the assignment might be a goto target
      i_it->make_skip();
      i_it++;

      while(!i_it->is_goto() && !i_it->is_end_function())
      {
        assert(i_it->is_dead());
        i_it++;
      }

      if(i_it->is_goto())
      {
        goto_programt::const_targett target=i_it->get_target();
        assert(target->is_end_function());
      }
      else
      {
        assert(i_it->is_end_function());
        i_it=goto_program.instructions.insert(i_it, *i_it);
      }

      i_it->make_return();
      i_it->code=return_code;
    }
  }

  return false;
}

/*******************************************************************\

Function: remove_returnst::undo_function_calls

Inputs:

Outputs:

Purpose: turns f(...); lhs=f#return_value; into x=f(...)

\*******************************************************************/

void remove_returnst::undo_function_calls(
  goto_functionst &goto_functions,
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(i_it->code);

      // ignore function pointers
      if(function_call.function().id()!=ID_symbol)
        continue;

      const irep_idt function_id=
        to_symbol_expr(function_call.function()).get_identifier();

      const symbolt &function_symbol=ns.lookup(function_id);

      // fix the type
      to_code_type(function_call.function().type()).return_type()=
        to_code_type(function_symbol.type).return_type();

      // find "f(...); lhs=f#return_value; DEAD f#return_value;"
      // and revert to "lhs=f(...);"
      goto_programt::instructionst::iterator next=i_it;
      ++next;
      assert(next!=goto_program.instructions.end());

      if(!next->is_assign())
        continue;

      const code_assignt &assign=to_code_assign(next->code);

      if(assign.rhs().id()!=ID_symbol)
        continue;

      irep_idt rv_name=id2string(function_id)+RETURN_VALUE_SUFFIX;
      const symbol_exprt &rhs=to_symbol_expr(assign.rhs());
      if(rhs.get_identifier()!=rv_name)
        continue;

      // restore the previous assignment
      function_call.lhs()=assign.lhs();

      // remove the assignment and subsequent dead
      // i_it remains valid
      next=goto_program.instructions.erase(next);
      assert(next!=goto_program.instructions.end());
      assert(next->is_dead());
      // i_it remains valid
      goto_program.instructions.erase(next);
    }
  }
}

/*******************************************************************\

Function: remove_returnst::restore()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void remove_returnst::restore(goto_functionst &goto_functions)
{
  // restore all types first
  bool unmodified=true;
  Forall_goto_functions(it, goto_functions)
    unmodified=restore_returns(it) && unmodified;

  if(!unmodified)
  {
    Forall_goto_functions(it, goto_functions)
      undo_function_calls(goto_functions, it->second.body);
  }
}

/*******************************************************************\

Function: restore_returns

Inputs:

Outputs:

Purpose: restores return statements

\*******************************************************************/

void restore_returns(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_returnst rr(symbol_table);
  rr.restore(goto_functions);
}
