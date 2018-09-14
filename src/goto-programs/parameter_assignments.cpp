/*******************************************************************\

Module: Add parameter assignments

Author: Daniel Kroening

Date:   September 2015

\*******************************************************************/

/// \file
/// Add parameter assignments

#include "parameter_assignments.h"

#include <util/std_expr.h>
#include <util/symbol_table.h>

class parameter_assignmentst
{
public:
  explicit parameter_assignmentst(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;

  void do_function_calls(
    goto_programt &goto_program);
};

/// turns x=f(...) into f(...); lhs=f#return_value;
void parameter_assignmentst::do_function_calls(
  goto_programt &goto_program)
{
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(i_it->code);

      // add x=y for f(y) where x is the parameter

      PRECONDITION(function_call.function().id() == ID_symbol);

      const irep_idt &identifier=
        to_symbol_expr(function_call.function()).get_identifier();

      // see if we have it
      const namespacet ns(symbol_table);
      const symbolt &function_symbol=ns.lookup(identifier);
      const code_typet &code_type=to_code_type(function_symbol.type);

      goto_programt tmp;

      for(std::size_t nr=0; nr<code_type.parameters().size(); nr++)
      {
        irep_idt p_identifier=code_type.parameters()[nr].get_identifier();

        if(p_identifier.empty())
          continue;

        if(nr<function_call.arguments().size())
        {
          goto_programt::targett t=tmp.add_instruction();
          t->make_assignment();
          t->source_location=i_it->source_location;
          const symbolt &lhs_symbol=ns.lookup(p_identifier);
          symbol_exprt lhs=lhs_symbol.symbol_expr();
          exprt rhs=function_call.arguments()[nr];
          if(rhs.type()!=lhs.type())
            rhs.make_typecast(lhs.type());
          t->code=code_assignt(lhs, rhs);
          t->function=i_it->function;
        }
      }

      std::size_t count=tmp.instructions.size();
      goto_program.insert_before_swap(i_it, tmp);

      for(; count!=0; count--) i_it++;
    }
  }
}

void parameter_assignmentst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    do_function_calls(it->second.body);
}

/// removes returns
void parameter_assignments(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  parameter_assignmentst rr(symbol_table);
  rr(goto_functions);
}

/// removes returns
void parameter_assignments(goto_modelt &goto_model)
{
  parameter_assignmentst rr(goto_model.symbol_table);
  rr(goto_model.goto_functions);
}
