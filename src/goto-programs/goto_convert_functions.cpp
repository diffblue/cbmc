/********************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include "goto_convert_functions.h"

#include <util/base_type.h>
#include <util/fresh_symbol.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/symbol_table_builder.h>

#include "goto_inline.h"

goto_convert_functionst::goto_convert_functionst(
  symbol_table_baset &_symbol_table,
  message_handlert &_message_handler):
  goto_convertt(_symbol_table, _message_handler)
{
}

goto_convert_functionst::~goto_convert_functionst()
{
}

void goto_convert_functionst::goto_convert(goto_functionst &functions)
{
  // warning! hash-table iterators are not stable

  typedef std::list<irep_idt> symbol_listt;
  symbol_listt symbol_list;

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(
      !symbol_pair.second.is_type && !symbol_pair.second.is_macro &&
      symbol_pair.second.type.id() == ID_code &&
      (symbol_pair.second.mode == ID_C || symbol_pair.second.mode == ID_cpp ||
       symbol_pair.second.mode == ID_java || symbol_pair.second.mode == "jsil"))
    {
      symbol_list.push_back(symbol_pair.first);
    }
  }

  for(const auto &id : symbol_list)
  {
    convert_function(id, functions.function_map[id]);
  }

  functions.compute_location_numbers();

  // this removes the parse tree of the bodies from memory
  #if 0
  for(const auto &symbol_pair, symbol_table.symbols)
  {
    if(!symbol_pair.second.is_type &&
       symbol_pair.second.type.id()==ID_code &&
       symbol_pair.second.value.is_not_nil())
    {
      symbol_pair.second.value=codet();
    }
  }
  #endif
}

bool goto_convert_functionst::hide(const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    for(const auto &label : i_it->labels)
      if(label == CPROVER_PREFIX "HIDE")
        return true;
  }

  return false;
}

void goto_convert_functionst::add_return(
  goto_functionst::goto_functiont &f,
  const source_locationt &source_location)
{
  #if 0
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_return())
    return; // not needed, we have one already

  // see if we have an unconditional goto at the end
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_goto() &&
     f.body.instructions.back().guard.is_true())
    return;
  #else

  if(!f.body.instructions.empty())
  {
    goto_programt::const_targett last_instruction=
      f.body.instructions.end();
    last_instruction--;

    while(true)
    {
      // unconditional goto, say from while(1)?
      if(last_instruction->is_goto() &&
         last_instruction->guard.is_true())
        return;

      // return?
      if(last_instruction->is_return())
        return;

      // advance if it's a 'dead' without branch target
      if(last_instruction->is_dead() &&
         last_instruction!=f.body.instructions.begin() &&
         !last_instruction->is_target())
        last_instruction--;
      else
        break; // give up
    }
  }

  #endif

  const side_effect_expr_nondett rhs(f.type.return_type(), source_location);

  goto_programt::targett t=f.body.add_instruction();
  t->make_return();
  t->code=code_returnt(rhs);
  t->source_location=source_location;
}

void goto_convert_functionst::convert_function(
  const irep_idt &identifier,
  goto_functionst::goto_functiont &f)
{
  const symbolt &symbol=ns.lookup(identifier);
  const irep_idt mode = symbol.mode;

  if(f.body_available())
    return; // already converted

  // make tmp variables local to function
  tmp_symbol_prefix=id2string(symbol.name)+"::$tmp";

  f.type=to_code_type(symbol.type);

  if(symbol.value.is_nil() ||
     symbol.is_compiled()) /* goto_inline may have removed the body */
    return;

  const codet &code=to_code(symbol.value);

  source_locationt end_location;

  if(code.get_statement()==ID_block)
    end_location=to_code_block(code).end_location();
  else
    end_location.make_nil();

  goto_programt tmp_end_function;
  goto_programt::targett end_function=tmp_end_function.add_instruction();
  end_function->type=END_FUNCTION;
  end_function->source_location=end_location;
  end_function->code.set(ID_identifier, identifier);

  targets=targetst();
  targets.set_return(end_function);
  targets.has_return_value=
    f.type.return_type().id()!=ID_empty &&
    f.type.return_type().id()!=ID_constructor &&
    f.type.return_type().id()!=ID_destructor;

  goto_convert_rec(code, f.body, mode);

  // add non-det return value, if needed
  if(targets.has_return_value)
    add_return(f, end_location);

  // handle SV-COMP's __VERIFIER_atomic_
  if(!f.body.instructions.empty() &&
      has_prefix(id2string(identifier), "__VERIFIER_atomic_"))
  {
    goto_programt::instructiont a_begin;
    a_begin.make_atomic_begin();
    a_begin.source_location=f.body.instructions.front().source_location;
    f.body.insert_before_swap(f.body.instructions.begin(), a_begin);

    goto_programt::targett a_end=f.body.add_instruction();
    a_end->make_atomic_end();
    a_end->source_location=end_location;

    Forall_goto_program_instructions(i_it, f.body)
    {
      if(i_it->is_goto() && i_it->get_target()->is_end_function())
        i_it->set_target(a_end);
    }
  }

  // add "end of function"
  f.body.destructive_append(tmp_end_function);

  // do function tags (they are empty at this point)
  f.update_instructions_function(identifier);

  f.body.update();

  if(hide(f.body))
    f.make_hidden();
}

void goto_convert(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(goto_model.symbol_table);

  goto_convert(
    symbol_table_builder, goto_model.goto_functions, message_handler);
}

void goto_convert(
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(symbol_table);

  goto_convert_functionst goto_convert_functions(
    symbol_table_builder, message_handler);

  goto_convert_functions.goto_convert(functions);
}

void goto_convert(
  const irep_idt &identifier,
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(symbol_table);

  goto_convert_functionst goto_convert_functions(
    symbol_table_builder, message_handler);

  goto_convert_functions.convert_function(
    identifier, functions.function_map[identifier]);
}
