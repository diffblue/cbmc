/********************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include "goto_convert_functions.h"

#include <util/expr_util.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/symbol_table_builder.h>

#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

goto_convert_functionst::goto_convert_functionst(
  symbol_table_baset &_symbol_table,
  message_handlert &_message_handler)
  : goto_convertt(_symbol_table, _message_handler)
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
       symbol_pair.second.mode == ID_java ||
       symbol_pair.second.mode == ID_statement_list))
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
  for(const auto &instruction : goto_program.instructions)
  {
    for(const auto &label : instruction.labels)
    {
      if(label == CPROVER_PREFIX "HIDE")
        return true;
    }
  }

  return false;
}

void goto_convert_functionst::add_return(
  goto_functionst::goto_functiont &f,
  const typet &return_type,
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
    goto_programt::const_targett last_instruction = f.body.instructions.end();
    last_instruction--;

    while(true)
    {
      // unconditional goto, say from while(1)?
      if(last_instruction->is_goto() && last_instruction->condition() == true)
      {
        return;
      }

      // return?
      if(last_instruction->is_set_return_value())
        return;

      // advance if it's a 'dead' without branch target
      if(
        last_instruction->is_dead() &&
        last_instruction != f.body.instructions.begin() &&
        !last_instruction->is_target())
        last_instruction--;
      else
        break; // give up
    }
  }

#endif

  side_effect_expr_nondett rhs(return_type, source_location);

  f.body.add(
    goto_programt::make_set_return_value(std::move(rhs), source_location));
}

void goto_convert_functionst::convert_function(
  const irep_idt &identifier,
  goto_functionst::goto_functiont &f)
{
  const symbolt &symbol = ns.lookup(identifier);
  const irep_idt mode = symbol.mode;

  if(f.body_available())
    return; // already converted

  // make tmp variables local to function
  tmp_symbol_prefix = id2string(symbol.name) + "::$tmp";

  // store the parameter identifiers in the goto functions
  const code_typet &code_type = to_code_type(symbol.type);
  f.set_parameter_identifiers(code_type);

  // Provide bodies for operator new/delete by generating goto
  // programs that delegate to __new/__delete.
  if(symbol.value.is_nil() && symbol.type.id() == ID_code)
  {
    const std::string sname = id2string(identifier);
    const auto &op_params = code_type.parameters();
    // The placement forms operator new(size, void*) and
    // operator delete(void*, void*) ([new.delete.placement]) take a trailing
    // pointer argument and neither allocate nor deallocate; they must not be
    // synthesised as (de)allocations.  All other allocation functions allocate
    // their first (size) argument and all other deallocation functions
    // deallocate their first (pointer) argument ([basic.stc.dynamic]); the
    // optional size_t / align_val_t / nothrow_t arguments are not used.
    const bool is_placement_form =
      op_params.size() >= 2 && op_params.back().type().id() == ID_pointer;
    irep_idt impl;
    if(is_placement_form)
    {
      // leave to its own body
    }
    else if(has_prefix(sname, "operatorcpp_new[]("))
      impl = "__new_array";
    else if(has_prefix(sname, "operatorcpp_new("))
      impl = "__new";
    else if(has_prefix(sname, "operatorcpp_delete[]("))
      impl = "__delete_array";
    else if(has_prefix(sname, "operatorcpp_delete("))
      impl = "__delete";
    if(!impl.empty() && symbol_table.has_symbol(impl))
    {
      const symbolt &impl_sym = symbol_table.lookup_ref(impl);
      const code_typet &impl_type = to_code_type(impl_sym.type);
      const auto &params = code_type.parameters();
      // Ensure every parameter has an identifier.  operator new/delete (and
      // their sized/aligned overloads) are frequently declared without
      // parameter names, leaving empty identifiers; the synthesised body uses
      // only the first parameter, but all parameters must be named for the
      // goto function (an empty identifier triggers a namespace lookup
      // failure downstream).
      bool created_param = false;
      for(std::size_t i = 0; i < params.size(); ++i)
      {
        if(!params[i].get_identifier().empty())
          continue;
        const irep_idt pid =
          id2string(identifier) + "::param" + std::to_string(i);
        symbolt param_sym;
        param_sym.name = pid;
        param_sym.base_name = "param" + std::to_string(i);
        param_sym.type = params[i].type();
        param_sym.mode = symbol.mode;
        param_sym.is_lvalue = true;
        param_sym.is_parameter = true;
        param_sym.is_thread_local = true;
        param_sym.is_file_local = true;
        symbol_table.get_writeable_ref(identifier)
          .type.add(ID_parameters)
          .get_sub()[i]
          .set(ID_C_identifier, pid);
        symbol_table.insert(std::move(param_sym));
        created_param = true;
      }
      if(created_param)
        f.set_parameter_identifiers(
          to_code_type(symbol_table.lookup_ref(identifier).type));
      const irep_idt param_id =
        params.empty() ? irep_idt()
                       : to_code_type(symbol_table.lookup_ref(identifier).type)
                           .parameters()[0]
                           .get_identifier();
      // Build goto program: call __new(param0) and return result
      if(impl_type.return_type().id() != ID_empty && !params.empty())
      {
        // tmp = __new(param0)
        const symbolt &tmp = new_tmp_symbol(
          code_type.return_type(), "rv", f.body, symbol.location, symbol.mode);
        exprt arg = symbol_exprt(param_id, params[0].type());
        arg = typecast_exprt::conditional_cast(
          arg, impl_type.parameters()[0].type());
        code_function_callt call(
          tmp.symbol_expr(), impl_sym.symbol_expr(), {std::move(arg)});
        goto_programt::targett t1 =
          f.body.add(goto_programt::make_function_call(call, symbol.location));
        (void)t1;
        // return tmp
        f.body.add(goto_programt::make_set_return_value(
          tmp.symbol_expr(), symbol.location));
        f.body.add(goto_programt::make_end_function(symbol.location));
      }
      else if(!params.empty())
      {
        // void function (delete): call __delete(param0)
        exprt arg = symbol_exprt(param_id, params[0].type());
        code_function_callt call(impl_sym.symbol_expr(), {std::move(arg)});
        f.body.add(goto_programt::make_function_call(call, symbol.location));
        f.body.add(goto_programt::make_end_function(symbol.location));
      }
      if(!f.body.empty())
        return;
    }
  }

  if(
    symbol.value.is_nil() || symbol.value.id() != ID_code ||
    symbol.is_compiled()) /* goto_inline may have removed the body */
    return;

  // Skip functions whose bodies contain unresolved C++ names, which
  // indicates incomplete template instantiation.
  // For user functions (non-system headers), strip only the offending
  // statements rather than discarding the entire body, so that
  // assertions and other verified code survive.
  if(
    has_subexpr(symbol.value, ID_cpp_name) ||
    has_subexpr(symbol.value, irep_idt("cpp-this")))
  {
    const std::string file = id2string(symbol.location.get_file());
    bool is_system =
      file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0;
    if(is_system)
    {
      // Strip offending statements instead of clearing the entire body.
      // This preserves the parts of the body that are type-checked.
    }
    // For user functions, remove statements with unresolved names.
    std::function<void(exprt &)> strip_unresolved = [&](exprt &expr)
    {
      if(expr.id() == ID_code && to_code(expr).get_statement() == ID_block)
      {
        auto &block = to_code_block(to_code(expr));
        auto &stmts = block.statements();
        stmts.erase(
          std::remove_if(
            stmts.begin(),
            stmts.end(),
            [](const codet &s)
            {
              return has_subexpr(static_cast<const exprt &>(s), ID_cpp_name) ||
                     has_subexpr(
                       static_cast<const exprt &>(s), irep_idt("cpp-this"));
            }),
          stmts.end());
        for(auto &s : stmts)
          strip_unresolved(static_cast<exprt &>(s));
      }
    };
    strip_unresolved(symbol_table.get_writeable_ref(identifier).value);
    // If the body is now empty or still has unresolved names, clear it.
    if(
      has_subexpr(symbol_table.lookup_ref(identifier).value, ID_cpp_name) ||
      has_subexpr(
        symbol_table.lookup_ref(identifier).value, irep_idt("cpp-this")))
    {
      symbol_table.get_writeable_ref(identifier).value.make_nil();
      return;
    }
  }

  // we have a body, make sure all parameter names are valid
  for(const auto &p : f.parameter_identifiers)
  {
    // Empty parameter identifiers can arise from incomplete C++ template
    // instantiations; skip converting such functions.
    if(p.empty())
      return;

    if(!symbol_table.has_symbol(p))
    {
      // Create a missing parameter symbol (can happen for C++ template
      // instantiations where 'this' parameter symbols are not generated).
      const auto &code_type = to_code_type(symbol.type);
      for(const auto &param : code_type.parameters())
      {
        if(param.get_identifier() == p)
        {
          symbolt param_symbol{p, param.type(), symbol.mode};
          param_symbol.base_name = param.get_base_name();
          param_symbol.is_parameter = true;
          param_symbol.is_lvalue = true;
          param_symbol.location = symbol.location;
          symbol_table.insert(std::move(param_symbol));
          break;
        }
      }
    }
    else
    {
      // Ensure existing parameter symbols have is_parameter set.
      // C++ destructor code generation may create parameter symbols
      // (e.g., base class 'this' pointers) without this flag.
      symbolt &existing = symbol_table.get_writeable_ref(p);
      if(!existing.is_parameter)
        existing.is_parameter = true;
    }
  }

  lifetimet parent_lifetime = lifetime;
  lifetime = identifier == INITIALIZE_FUNCTION ? lifetimet::STATIC_GLOBAL
                                               : lifetimet::AUTOMATIC_LOCAL;

  const codet &code = to_code(symbol.value);

  source_locationt end_location;

  if(code.get_statement() == ID_block)
    end_location = to_code_block(code).end_location();
  else
    end_location.make_nil();

  goto_programt tmp_end_function;
  goto_programt::targett end_function =
    tmp_end_function.add(goto_programt::make_end_function(end_location));

  targets = targetst();
  targets.prefix = &f.body;
  targets.suffix = &tmp_end_function;
  targets.set_return(end_function);
  targets.has_return_value = code_type.return_type().id() != ID_empty &&
                             code_type.return_type().id() != ID_constructor &&
                             code_type.return_type().id() != ID_destructor;

  goto_convert_rec(code, f.body, mode);

  // add non-det return value, if needed
  if(targets.has_return_value)
    add_return(f, code_type.return_type(), end_location);

  // handle SV-COMP's __VERIFIER_atomic_
  if(
    !f.body.instructions.empty() &&
    identifier.starts_with("__VERIFIER_atomic_"))
  {
    goto_programt::instructiont a_begin = goto_programt::make_atomic_begin(
      f.body.instructions.front().source_location());
    f.body.insert_before_swap(f.body.instructions.begin(), a_begin);

    goto_programt::targett a_end =
      f.body.add(goto_programt::make_atomic_end(end_location));

    for(auto &instruction : f.body.instructions)
    {
      if(instruction.is_goto() && instruction.get_target()->is_end_function())
        instruction.set_target(a_end);
    }
  }

  // add "end of function"
  f.body.destructive_append(tmp_end_function);

  f.body.update();

  if(hide(f.body))
    f.make_hidden();

  lifetime = parent_lifetime;

  targets.prefix = nullptr;
  targets.suffix = nullptr;
}

void goto_convert(goto_modelt &goto_model, message_handlert &message_handler)
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
