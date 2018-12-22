/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Remove Virtual Function (Method) Calls
#include "remove_virtual_functions.h"

#include <algorithm>

#include <util/type_eq.h>

#include "class_identifier.h"
#include "goto_model.h"
#include "remove_skip.h"
#include "resolve_inherited_component.h"

class remove_virtual_functionst
{
public:
  remove_virtual_functionst(
    const symbol_table_baset &_symbol_table,
    const class_hierarchyt &_class_hierarchy);

  void operator()(goto_functionst &goto_functions);

  bool remove_virtual_functions(goto_programt &goto_program);

  goto_programt::targett remove_virtual_function(
    goto_programt &goto_program,
    goto_programt::targett target,
    const dispatch_table_entriest &functions,
    virtual_dispatch_fallback_actiont fallback_action);

  void get_functions(const exprt &, dispatch_table_entriest &);

protected:
  const namespacet ns;
  const symbol_table_baset &symbol_table;

  const class_hierarchyt &class_hierarchy;

  goto_programt::targett remove_virtual_function(
    goto_programt &goto_program,
    goto_programt::targett target);
  typedef std::function<
    resolve_inherited_componentt::inherited_componentt(
      const irep_idt &,
      const irep_idt &)>
    function_call_resolvert;
  void get_child_functions_rec(
    const irep_idt &,
    const symbol_exprt &,
    const irep_idt &,
    dispatch_table_entriest &,
    dispatch_table_entries_mapt &,
    const function_call_resolvert &) const;
  exprt
  get_method(const irep_idt &class_id, const irep_idt &component_name) const;
};

remove_virtual_functionst::remove_virtual_functionst(
  const symbol_table_baset &_symbol_table,
  const class_hierarchyt &_class_hierarchy)
  : ns(_symbol_table),
    symbol_table(_symbol_table),
    class_hierarchy(_class_hierarchy)
{
}

/// Replace specified virtual function call with a static call to its
/// most derived implementation
/// \param [in,out] goto_program: GOTO program to modify
/// \param target: iterator to a function in the supplied GOTO program
/// to replace. Must point to a virtual function call.
/// \return Returns a pointer to the statement in the supplied GOTO
/// program after replaced function call
goto_programt::targett remove_virtual_functionst::remove_virtual_function(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &code=
    to_code_function_call(target->code);

  const exprt &function=code.function();
  INVARIANT(
    function.id()==ID_virtual_function,
    "remove_virtual_function must take a virtual function call instruction");
  INVARIANT(
    !code.arguments().empty(),
    "virtual function calls must have at least a this-argument");

  dispatch_table_entriest functions;
  get_functions(function, functions);

  return remove_virtual_function(
    goto_program,
    target,
    functions,
    virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION);
}

/// Create a concrete function call to replace a virtual one
/// \param [in,out] call: the function call to update
/// \param function_symbol: the function to be called
/// \param ns: namespace
static void create_static_function_call(
  code_function_callt &call,
  const symbol_exprt &function_symbol,
  const namespacet &ns)
{
  call.function() = function_symbol;
  // Cast the `this` pointer to the correct type for the new callee:
  const auto &callee_type =
    to_code_type(ns.lookup(function_symbol.get_identifier()).type);
  const code_typet::parametert *this_param = callee_type.get_this();
  INVARIANT(
    this_param != nullptr,
    "Virtual function callees must have a `this` argument");
  typet need_type = this_param->type();
  if(!type_eq(call.arguments()[0].type(), need_type, ns))
    call.arguments()[0].make_typecast(need_type);
}

/// Replace virtual function call with a static function call
/// Achieved by substituting a virtual function with its most derived
/// implementation. If there's a type mismatch between implementation
/// and the instance type or if fallback_action is set to
/// ASSUME_FALSE, then function is substituted with a call to ASSUME(false)
/// \param [in,out] goto_program: GOTO program to modify
/// \param target: Iterator to the GOTO instruction in the supplied
/// GOTO program to be removed. Must point to a function call
/// \param functions: Dispatch table - all possible implementations of
/// this function sorted from the least to the most derived
/// \param fallback_action: - ASSUME_FALSE to replace virtual function
/// calls with ASSUME(false) or CALL_LAST_FUNCTION to replace them
/// with the most derived matching call
/// \return Returns a pointer to the statement in the supplied GOTO
/// program after replaced function call
goto_programt::targett remove_virtual_functionst::remove_virtual_function(
  goto_programt &goto_program,
  goto_programt::targett target,
  const dispatch_table_entriest &functions,
  virtual_dispatch_fallback_actiont fallback_action)
{
  INVARIANT(
    target->is_function_call(),
    "remove_virtual_function must target a FUNCTION_CALL instruction");
  const code_function_callt &code=
    to_code_function_call(target->code);

  goto_programt::targett next_target = std::next(target);

  if(functions.empty())
  {
    target->make_skip();
    remove_skip(goto_program, target, next_target);
    return next_target; // give up
  }

  // only one option?
  if(functions.size()==1 &&
     fallback_action==virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION)
  {
    if(functions.begin()->symbol_expr==symbol_exprt())
    {
      target->make_skip();
      remove_skip(goto_program, target, next_target);
    }
    else
    {
      create_static_function_call(
        to_code_function_call(target->code), functions.front().symbol_expr, ns);
    }
    return next_target;
  }

  const auto &vcall_source_loc=target->source_location;

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final=final_skip.add_instruction();
  t_final->source_location=vcall_source_loc;

  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  exprt this_expr=code.arguments()[0];
  const auto &last_function_symbol=functions.back().symbol_expr;

  const typet &this_type=this_expr.type();
  INVARIANT(this_type.id() == ID_pointer, "this parameter must be a pointer");
  INVARIANT(
    this_type.subtype() != empty_typet(),
    "this parameter must not be a void pointer");

  // So long as `this` is already not `void*` typed, the second parameter
  // is ignored:
  exprt this_class_identifier =
    get_class_identifier_field(this_expr, struct_tag_typet(irep_idt()), ns);

  // If instructed, add an ASSUME(FALSE) to handle the case where we don't
  // match any expected type:
  if(fallback_action==virtual_dispatch_fallback_actiont::ASSUME_FALSE)
  {
    auto newinst=new_code_calls.add_instruction(ASSUME);
    newinst->guard=false_exprt();
    newinst->source_location=vcall_source_loc;
  }

  // get initial identifier for grouping
  INVARIANT(!functions.empty(), "Function dispatch table cannot be empty.");

  std::map<irep_idt, goto_programt::targett> calls;
  // Note backwards iteration, to get the fallback candidate first.
  for(auto it=functions.crbegin(), itend=functions.crend(); it!=itend; ++it)
  {
    const auto &fun=*it;
    auto insertit=calls.insert(
      {fun.symbol_expr.get_identifier(), goto_programt::targett()});

    // Only create one call sequence per possible target:
    if(insertit.second)
    {
      goto_programt::targett t1=new_code_calls.add_instruction();
      t1->source_location=vcall_source_loc;
      if(!fun.symbol_expr.get_identifier().empty())
      {
      // call function
        t1->make_function_call(code);
        create_static_function_call(
          to_code_function_call(t1->code), fun.symbol_expr, ns);
      }
      else
      {
        // No definition for this type; shouldn't be possible...
        t1->make_assertion(false_exprt());
        t1->source_location.set_comment(
          "cannot find calls for " +
          id2string(code.function().get(ID_identifier)) + " dispatching " +
          id2string(fun.class_id));
      }
      insertit.first->second=t1;
      // goto final
      goto_programt::targett t3=new_code_calls.add_instruction();
      t3->source_location=vcall_source_loc;
      t3->make_goto(t_final, true_exprt());
    }

    // Fall through to the default callee if possible:
    if(fallback_action ==
       virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION &&
       fun.symbol_expr == last_function_symbol)
    {
      // Nothing to do
    }
    else
    {
      const constant_exprt fun_class_identifier(fun.class_id, string_typet());
      const equal_exprt class_id_test(
        fun_class_identifier, this_class_identifier);

      // If the previous GOTO goes to the same callee, join it
      // (e.g. turning IF x GOTO y into IF x || z GOTO y)
      if(it != functions.crbegin() &&
         std::prev(it)->symbol_expr == fun.symbol_expr)
      {
        INVARIANT(
          !new_code_gotos.empty(),
          "a dispatch table entry has been processed already, "
          "which should have created a GOTO");
        new_code_gotos.instructions.back().guard =
          or_exprt(new_code_gotos.instructions.back().guard, class_id_test);
      }
      else
      {
        goto_programt::targett new_goto = new_code_gotos.add_instruction();
        new_goto->source_location = vcall_source_loc;
        new_goto->make_goto(insertit.first->second, class_id_test);
      }
    }
  }

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  // set locations
  Forall_goto_program_instructions(it, new_code)
  {
    const irep_idt property_class=it->source_location.get_property_class();
    const irep_idt comment=it->source_location.get_comment();
    it->source_location=target->source_location;
    it->function=target->function;
    if(!property_class.empty())
      it->source_location.set_property_class(property_class);
    if(!comment.empty())
      it->source_location.set_comment(comment);
  }

  goto_program.destructive_insert(next_target, new_code);

  // finally, kill original invocation
  target->make_skip();

  // only remove skips within the virtual-function handling block
  remove_skip(goto_program, target, next_target);

  return next_target;
}

/// Used by get_functions to track the most-derived parent that provides an
/// override of a given function.
/// \param this_id: class name
/// \param last_method_defn: the most-derived parent of `this_id` to define
///   the requested function
/// \param component_name: name of the function searched for
/// \param [out] functions: `functions` is assigned a list of
///   {class name, function symbol} pairs indicating that if `this` is of the
///   given class, then the call will target the given function. Thus if
///   A <: B <: C and A and C provide overrides of `f` (but B does not),
///   get_child_functions_rec("C", C.f, "f")
///   -> [{"C", C.f}, {"B", C.f}, {"A", A.f}]
/// \param entry_map: map of class identifiers to dispatch table entries
/// \param resolve_function_call`: function to resolve abstract method call
void remove_virtual_functionst::get_child_functions_rec(
  const irep_idt &this_id,
  const symbol_exprt &last_method_defn,
  const irep_idt &component_name,
  dispatch_table_entriest &functions,
  dispatch_table_entries_mapt &entry_map,
  const function_call_resolvert &resolve_function_call) const
{
  auto findit=class_hierarchy.class_map.find(this_id);
  if(findit==class_hierarchy.class_map.end())
    return;

  for(const auto &child : findit->second.children)
  {
    // Skip if we have already visited this and we found a function call that
    // did not resolve to non java.lang.Object.
    auto it = entry_map.find(child);
    if(
      it != entry_map.end() &&
      !has_prefix(
        id2string(it->second.symbol_expr.get_identifier()),
        "java::java.lang.Object"))
    {
      continue;
    }
    exprt method = get_method(child, component_name);
    dispatch_table_entryt function(child);
    if(method.is_not_nil())
    {
      function.symbol_expr=to_symbol_expr(method);
      function.symbol_expr.set(ID_C_class, child);
    }
    else
    {
      function.symbol_expr=last_method_defn;
    }
    if(function.symbol_expr == symbol_exprt())
    {
      const resolve_inherited_componentt::inherited_componentt
        &resolved_call = resolve_function_call(child, component_name);
      if(resolved_call.is_valid())
      {
        function.class_id = resolved_call.get_class_identifier();
        const symbolt &called_symbol =
          symbol_table.lookup_ref(
            resolved_call.get_full_component_identifier());

        function.symbol_expr = called_symbol.symbol_expr();
        function.symbol_expr.set(
          ID_C_class, resolved_call.get_class_identifier());
      }
    }
    functions.push_back(function);
    entry_map.insert({child, function});

    get_child_functions_rec(
      child,
      function.symbol_expr,
      component_name,
      functions,
      entry_map,
      resolve_function_call);
  }
}

/// Used to get dispatch entries to call for the given function
/// \param function: function that should be called
/// \param [out] functions: is assigned a list of dispatch entries, i.e., pairs
/// of class names and function symbol to call when encountering the class.
void remove_virtual_functionst::get_functions(
  const exprt &function,
  dispatch_table_entriest &functions)
{
  // class part of function to call
  const irep_idt class_id=function.get(ID_C_class);
  const std::string class_id_string(id2string(class_id));
  const irep_idt function_name = function.get(ID_component_name);
  const std::string function_name_string(id2string(function_name));
  INVARIANT(!class_id.empty(), "All virtual functions must have a class");

  resolve_inherited_componentt get_virtual_call_target(
    symbol_table, class_hierarchy);
  const function_call_resolvert resolve_function_call =
    [&get_virtual_call_target](
      const irep_idt &class_id, const irep_idt &function_name) {
    return get_virtual_call_target(class_id, function_name, false);
    };

  const resolve_inherited_componentt::inherited_componentt
    &resolved_call = get_virtual_call_target(class_id, function_name, false);

  dispatch_table_entryt root_function;

  if(resolved_call.is_valid())
  {
    root_function.class_id=resolved_call.get_class_identifier();

    const symbolt &called_symbol =
      symbol_table.lookup_ref(resolved_call.get_full_component_identifier());

    root_function.symbol_expr=called_symbol.symbol_expr();
    root_function.symbol_expr.set(
      ID_C_class, resolved_call.get_class_identifier());
  }
  else
  {
    // No definition here; this is an abstract function.
    root_function.class_id=class_id;
  }

  // iterate over all children, transitively
  dispatch_table_entries_mapt entry_map;
  get_child_functions_rec(
    class_id,
    root_function.symbol_expr,
    function_name,
    functions,
    entry_map,
    resolve_function_call);

  if(root_function.symbol_expr!=symbol_exprt())
    functions.push_back(root_function);

  // Sort for the identifier of the function call symbol expression, grouping
  // together calls to the same function. Keep java.lang.Object entries at the
  // end for fall through. The reasoning is that this is the case with most
  // entries in realistic cases.
  std::sort(
    functions.begin(),
    functions.end(),
    [](const dispatch_table_entryt &a, dispatch_table_entryt &b)
    {
      if(
        has_prefix(
          id2string(a.symbol_expr.get_identifier()), "java::java.lang.Object"))
        return false;
      else if(
        has_prefix(
          id2string(b.symbol_expr.get_identifier()), "java::java.lang.Object"))
        return true;
      else
      {
        int cmp = a.symbol_expr.get_identifier().compare(
          b.symbol_expr.get_identifier());
        if(cmp == 0)
          return a.class_id < b.class_id;
        else
          return cmp < 0;
      }
    });
}

/// Returns symbol pointing to a specified method in a specified class
/// \param class_id: Class identifier to look up
/// \param component_name: Name of the function to look up
/// \return nil_exprt instance on error and a symbol_exprt pointing to
/// the method on success
exprt remove_virtual_functionst::get_method(
  const irep_idt &class_id,
  const irep_idt &component_name) const
{
  const irep_idt &id=
    resolve_inherited_componentt::build_full_component_identifier(
      class_id, component_name);

  const symbolt *symbol;
  if(ns.lookup(id, symbol))
    return nil_exprt();

  return symbol->symbol_expr();
}

/// Remove all virtual function calls in a GOTO program and replace
/// them with calls to their most derived implementations. Returns
/// true if at least one function has been replaced.
bool remove_virtual_functionst::remove_virtual_functions(
  goto_programt &goto_program)
{
  bool did_something=false;

  for(goto_programt::instructionst::iterator
      target = goto_program.instructions.begin();
      target != goto_program.instructions.end();
      ) // remove_virtual_function returns the next instruction to process
  {
    if(target->is_function_call())
    {
      const code_function_callt &code=
        to_code_function_call(target->code);

      if(code.function().id()==ID_virtual_function)
      {
        target = remove_virtual_function(goto_program, target);
        did_something=true;
        continue;
      }
    }

    ++target;
  }

  if(did_something)
    goto_program.update();

  return did_something;
}

/// Remove virtual function calls from all functions in the specified
/// list and replace them with their most derived implementations
void remove_virtual_functionst::operator()(goto_functionst &functions)
{
  bool did_something=false;

  for(goto_functionst::function_mapt::iterator f_it=
      functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;

    if(remove_virtual_functions(goto_program))
      did_something=true;
  }

  if(did_something)
    functions.compute_location_numbers();
}

/// Remove virtual function calls from all functions in the specified
/// list and replace them with their most derived implementations
void remove_virtual_functions(
  const symbol_table_baset &symbol_table,
  goto_functionst &goto_functions)
{
  class_hierarchyt class_hierarchy;
  class_hierarchy(symbol_table);
  remove_virtual_functionst rvf(symbol_table, class_hierarchy);
  rvf(goto_functions);
}

/// Remove virtual function calls from the specified model
void remove_virtual_functions(goto_modelt &goto_model)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions);
}

/// Remove virtual function calls from the specified model function
void remove_virtual_functions(goto_model_functiont &function)
{
  class_hierarchyt class_hierarchy;
  class_hierarchy(function.get_symbol_table());
  remove_virtual_functionst rvf(function.get_symbol_table(), class_hierarchy);
  rvf.remove_virtual_functions(function.get_goto_function().body);
}

/// Replace virtual function call with a static function call
/// Achieved by substituting a virtual function with its most derived
/// implementation. If there's a type mismatch between implementation
/// and the instance type or if fallback_action is set to
/// ASSUME_FALSE, then function is substituted with a call to ASSUME(false)
/// \param symbol_table: Symbol table
/// \param [in,out] goto_program: GOTO program to modify
/// \param instruction: Iterator to the GOTO instruction in the supplied
/// GOTO program to be removed. Must point to a function call
/// \param dispatch_table: Dispatch table - all possible implementations of
/// this function sorted from the least to the most derived
/// \param fallback_action: - ASSUME_FALSE to replace virtual function
/// calls with ASSUME(false) or CALL_LAST_FUNCTION to replace them
/// with the most derived matching call
/// \return Returns a pointer to the statement in the supplied GOTO
/// program after replaced function call
goto_programt::targett remove_virtual_function(
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action)
{
  class_hierarchyt class_hierarchy;
  class_hierarchy(symbol_table);
  remove_virtual_functionst rvf(symbol_table, class_hierarchy);

  goto_programt::targett next = rvf.remove_virtual_function(
    goto_program, instruction, dispatch_table, fallback_action);

  goto_program.update();

  return next;
}

goto_programt::targett remove_virtual_function(
  goto_modelt &goto_model,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action)
{
  return remove_virtual_function(
    goto_model.symbol_table,
    goto_program,
    instruction,
    dispatch_table,
    fallback_action);
}

void collect_virtual_function_callees(
  const exprt &function,
  const symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  dispatch_table_entriest &overridden_functions)
{
  remove_virtual_functionst instance(symbol_table, class_hierarchy);
  instance.get_functions(function, overridden_functions);
}
