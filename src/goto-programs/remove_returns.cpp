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

protected:
  symbol_tablet &symbol_table;

  void do_return_value(
    goto_functionst::function_mapt::iterator f_it);

  void do_function_calls(
    goto_functionst &goto_functions,
    goto_programt &goto_program);
};

/*******************************************************************\

Function: remove_returnst::do_return_value

Inputs:

Outputs:

Purpose: turns 'return x' into an assignment to fkt#return_value
         and a 'goto the_end_of_the_function'

\*******************************************************************/

void remove_returnst::do_return_value(
  goto_functionst::function_mapt::iterator f_it)
{
  typet return_type=f_it->second.type.return_type();

  const irep_idt function_id=f_it->first;

  // returns something but void?
  if(return_type!=empty_typet())
  {
    // look up the function symbol
    symbol_tablet::symbolst::iterator s_it=
      symbol_table.symbols.find(function_id);

    assert(s_it!=symbol_table.symbols.end());
    symbolt &function_symbol=s_it->second;

    // make the return type 'void'
    f_it->second.type.return_type()=empty_typet();
    function_symbol.type=f_it->second.type;

    // add symbol to symbol_table
    symbolt new_symbol;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.is_thread_local=true;
    new_symbol.is_file_local=true;
    new_symbol.is_static_lifetime=true;
    new_symbol.module=function_symbol.module;
    new_symbol.value.make_nil();
    new_symbol.base_name=id2string(function_symbol.base_name)+"#return_value";
    new_symbol.name=id2string(function_symbol.name)+"#return_value";
    new_symbol.mode=function_symbol.mode;
    new_symbol.type=return_type;

    symbol_table.add(new_symbol);
  }

  goto_programt &goto_program=f_it->second.body;
  
  if(goto_program.empty())
    return;

  goto_programt::targett end_function=
    --goto_program.instructions.end();

  assert(end_function->is_end_function());

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_return())
    {
      assert(i_it->code.operands().size()==1);

      // replace "return x;" by "fkt#return_value=x; goto end_function;"
      symbol_exprt lhs_expr;
      lhs_expr.set_identifier(id2string(function_id)+"#return_value");
      lhs_expr.type()=return_type;

      code_assignt assignment(lhs_expr, i_it->code.op0());

      // now turn return into goto
      i_it->make_goto(end_function);

      goto_programt::instructiont tmp_i;
      tmp_i.make_assignment();
      tmp_i.code=assignment;
      tmp_i.location=i_it->location;
      tmp_i.function=i_it->function;

      // inserts the assignment
      goto_program.insert_before_swap(i_it, tmp_i);

      i_it++;
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

      assert(function_call.function().id()==ID_symbol);

      const irep_idt function_id=
        to_symbol_expr(function_call.function()).get_identifier();

      // see if we have a body
      goto_functionst::function_mapt::const_iterator
        f_it=goto_functions.function_map.find(function_id);

      if(f_it==goto_functions.function_map.end())
        throw "failed to find function in function map";

      if(f_it->second.body_available)
      {
        // replace "lhs=f(...)" by "f(...); lhs=f#return_value;"
        code_typet old_type=to_code_type(function_call.function().type());

        if(old_type.return_type()!=empty_typet())
        {
          // fix the type
          to_code_type(function_call.function().type()).return_type()=empty_typet();

          if(function_call.lhs().is_not_nil())
          {
            symbol_exprt rhs;
            rhs.type()=function_call.lhs().type();
            rhs.set_identifier(id2string(function_id)+"#return_value");

            goto_programt::targett t=goto_program.insert_after(i_it);
            t->make_assignment();
            t->location=i_it->location;
            t->code=code_assignt(function_call.lhs(), rhs);
            t->function=i_it->function;

            // fry the previous assignment
            function_call.lhs().make_nil();
          }
        }
      }
      else // no body available
      {
        goto_programt tmp;

        // evaluate function arguments -- they might have
        // pointer dereferencing or the like
        const exprt::operandst &arguments=function_call.arguments();
        forall_expr(a_it, arguments)
        {
          goto_programt::targett t=tmp.add_instruction();
          t->make_other();
          t->location=i_it->location;
          t->function=i_it->function;
          t->code=codet(ID_expression);
          t->code.copy_to_operands(*a_it);
        }

        // return value
        if(function_call.lhs().is_not_nil())
        {
          exprt rhs=side_effect_expr_nondett(function_call.lhs().type());
          rhs.location()=i_it->location;

          code_assignt code(function_call.lhs(), rhs);
          code.location()=i_it->location;

          goto_programt::targett t=tmp.add_instruction(ASSIGN);
          t->location=i_it->location;
          t->function=i_it->function;
          t->code.swap(code);
        }

        // now just kill call
        i_it->type=LOCATION;
        i_it->code.clear();        

        // insert tmp
        goto_programt::targett next=i_it; next++;
        goto_program.destructive_insert(next, tmp);
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
    do_return_value(it);
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

