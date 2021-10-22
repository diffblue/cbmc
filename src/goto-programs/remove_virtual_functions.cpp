/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Remove Virtual Function (Method) Calls
#include "remove_virtual_functions.h"

#include <algorithm>

#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/prefix.h>
#include <util/symbol_table.h>

#include "class_hierarchy.h"
#include "class_identifier.h"
#include "goto_model.h"
#include "remove_skip.h"
#include "resolve_inherited_component.h"

class get_virtual_calleest
{
public:
  get_virtual_calleest(
    const symbol_table_baset &_symbol_table,
    const class_hierarchyt &_class_hierarchy)
    : ns(_symbol_table),
      symbol_table(_symbol_table),
      class_hierarchy(_class_hierarchy)
  {
  }

  void get_functions(const exprt &, dispatch_table_entriest &) const;

private:
  const namespacet ns;
  const symbol_table_baset &symbol_table;

  const class_hierarchyt &class_hierarchy;

  typedef std::function<
    optionalt<resolve_inherited_componentt::inherited_componentt>(
      const irep_idt &,
      const irep_idt &)>
    function_call_resolvert;
  void get_child_functions_rec(
    const irep_idt &,
    const optionalt<symbol_exprt> &,
    const irep_idt &,
    dispatch_table_entriest &,
    dispatch_table_entries_mapt &) const;
  exprt
  get_method(const irep_idt &class_id, const irep_idt &component_name) const;
};

class remove_virtual_functionst
{
public:
  remove_virtual_functionst(
    symbol_table_baset &_symbol_table,
    const class_hierarchyt &_class_hierarchy)
    : class_hierarchy(_class_hierarchy),
      symbol_table(_symbol_table),
      ns(symbol_table)
  {
  }

  void operator()(goto_functionst &functions);

  bool remove_virtual_functions(
    const irep_idt &function_id,
    goto_programt &goto_program);

private:
  const class_hierarchyt &class_hierarchy;
  symbol_table_baset &symbol_table;
  namespacet ns;

  goto_programt::targett remove_virtual_function(
    const irep_idt &function_id,
    goto_programt &goto_program,
    goto_programt::targett target);
};

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
  // Cast the pointers to the correct type for the new callee:
  // Note the `this` pointer is expected to change type, but other pointers
  // could also change due to e.g. using a different alias to refer to the same
  // type (in Java, for example, we see ArrayList.add(ArrayList::E arg)
  // overriding Collection.add(Collection::E arg))
  const auto &callee_parameters =
    to_code_type(ns.lookup(function_symbol.get_identifier()).type).parameters();
  auto &call_args = call.arguments();

  INVARIANT(
    callee_parameters.size() == call_args.size(),
    "function overrides must have matching argument counts");

  for(std::size_t i = 0; i < call_args.size(); ++i)
  {
    const typet &need_type = callee_parameters[i].type();

    if(call_args[i].type() != need_type)
    {
      // If this wasn't language agnostic code we'd also like to check
      // compatibility-- for example, Java overrides may have differing generic
      // qualifiers, but not different base types.
      INVARIANT(
        call_args[i].type().id() == ID_pointer,
        "where overriding function argument types differ, "
        "those arguments must be pointer-typed");
      call_args[i] = typecast_exprt(call_args[i], need_type);
    }
  }
}

/// Duplicate ASSUME instructions involving \p argument_for_this for
/// \p temp_var_for_this. We only look at the ASSERT and ASSUME instructions
/// which directly precede the virtual function call. This is mainly aimed at
/// null checks, because \ref local_safe_pointerst would otherwise lose track
/// of known-not-null pointers due to the newly introduced assignment.
/// \param goto_program: The goto program containing the virtual function call
/// \param instr_it: Iterator to the virtual function call in \p goto_program
/// \param argument_for_this: The original expression for the this argument of
///   the virtual function call
/// \param temp_var_for_this: The new expression for the this argument of the
///   virtual function call
/// \return A goto program consisting of all the amended asserts and assumes
static goto_programt analyse_checks_directly_preceding_function_call(
  const goto_programt &goto_program,
  goto_programt::const_targett instr_it,
  const exprt &argument_for_this,
  const symbol_exprt &temp_var_for_this)
{
  goto_programt checks_directly_preceding_function_call;

  while(instr_it != goto_program.instructions.cbegin())
  {
    instr_it = std::prev(instr_it);

    if(instr_it->is_assert())
    {
      continue;
    }

    if(!instr_it->is_assume())
    {
      break;
    }

    exprt guard = instr_it->get_condition();

    bool changed = false;
    for(auto expr_it = guard.depth_begin(); expr_it != guard.depth_end();
        ++expr_it)
    {
      if(*expr_it == argument_for_this)
      {
        expr_it.mutate() = temp_var_for_this;
        changed = true;
      }
    }

    if(changed)
    {
      checks_directly_preceding_function_call.insert_before(
        checks_directly_preceding_function_call.instructions.cbegin(),
        goto_programt::make_assumption(guard));
    }
  }

  return checks_directly_preceding_function_call;
}

/// If \p argument_for_this contains a dereference then create a temporary
/// variable for it and use that instead
/// \param function_id: The identifier of the function we are currently
///   analysing
/// \param goto_program: The goto program containing the virtual function call
/// \param target: Iterator to the virtual function call in \p goto_program
/// \param [in,out] argument_for_this: The first argument of the function call
/// \param symbol_table: The symbol table to add the new symbol to
/// \param vcall_source_loc: The source location of the function call, which is
///   used for new instructions that are added
/// \param [out] new_code_for_this_argument: New instructions are added here
static void process_this_argument(
  const irep_idt &function_id,
  const goto_programt &goto_program,
  const goto_programt::targett target,
  exprt &argument_for_this,
  symbol_table_baset &symbol_table,
  const source_locationt &vcall_source_loc,
  goto_programt &new_code_for_this_argument)
{
  if(has_subexpr(argument_for_this, ID_dereference))
  {
    // Create a temporary for the `this` argument. This is so that
    // \ref goto_symext::try_filter_value_sets can reduce the value-set for
    // `this` to those elements with the correct class identifier.
    symbolt &temp_symbol = get_fresh_aux_symbol(
      argument_for_this.type(),
      id2string(function_id),
      "this_argument",
      vcall_source_loc,
      symbol_table.lookup_ref(function_id).mode,
      symbol_table);
    const symbol_exprt temp_var_for_this = temp_symbol.symbol_expr();

    new_code_for_this_argument.add(
      goto_programt::make_decl(temp_var_for_this, vcall_source_loc));
    new_code_for_this_argument.add(
      goto_programt::make_assignment(
        temp_var_for_this, argument_for_this, vcall_source_loc));

    goto_programt checks_directly_preceding_function_call =
      analyse_checks_directly_preceding_function_call(
        goto_program, target, argument_for_this, temp_var_for_this);

    new_code_for_this_argument.destructive_append(
      checks_directly_preceding_function_call);

    argument_for_this = temp_var_for_this;
  }
}

/// Replace virtual function call with a static function call
/// Achieved by substituting a virtual function with its most derived
/// implementation. If there's a type mismatch between implementation
/// and the instance type or if fallback_action is set to
/// ASSUME_FALSE, then function is substituted with a call to ASSUME(false)
/// \param symbol_table: Symbol table associated with \p goto_program
/// \param function_id: The identifier of the function we are currently
///   analysing
/// \param [in,out] goto_program: GOTO program to modify
/// \param target: Iterator to the GOTO instruction in the supplied
///   GOTO program to be removed. Must point to a function call
/// \param functions: Dispatch table - all possible implementations of
///   this function sorted from the least to the most derived
/// \param fallback_action: - ASSUME_FALSE to replace virtual function
///   calls with ASSUME(false) or CALL_LAST_FUNCTION to replace them
///   with the most derived matching call
/// \return Returns a pointer to the statement in the supplied GOTO
///   program after replaced function call
static goto_programt::targett replace_virtual_function_with_dispatch_table(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett target,
  const dispatch_table_entriest &functions,
  virtual_dispatch_fallback_actiont fallback_action)
{
  INVARIANT(
    target->is_function_call(),
    "remove_virtual_function must target a FUNCTION_CALL instruction");

  namespacet ns(symbol_table);
  goto_programt::targett next_target = std::next(target);

  if(functions.empty())
  {
    target->turn_into_skip();
    remove_skip(goto_program, target, next_target);
    return next_target; // give up
  }

  // only one option?
  if(functions.size()==1 &&
     fallback_action==virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION)
  {
    if(!functions.front().symbol_expr.has_value())
    {
      target->turn_into_skip();
      remove_skip(goto_program, target, next_target);
    }
    else
    {
      auto c = code_function_callt(
        target->call_lhs(), target->call_function(), target->call_arguments());
      create_static_function_call(c, *functions.front().symbol_expr, ns);
      target->call_function() = c.function();
      target->call_arguments() = c.arguments();
    }
    return next_target;
  }

  const auto &vcall_source_loc = target->source_location();

  code_function_callt code(
    target->call_lhs(), target->call_function(), target->call_arguments());
  goto_programt new_code_for_this_argument;

  process_this_argument(
    function_id,
    goto_program,
    target,
    code.arguments()[0],
    symbol_table,
    vcall_source_loc,
    new_code_for_this_argument);

  const exprt &this_expr = code.arguments()[0];

  // Create a skip as the final target for each branch to jump to at the end
  goto_programt final_skip;

  goto_programt::targett t_final =
    final_skip.add(goto_programt::make_skip(vcall_source_loc));

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  INVARIANT(
    this_expr.type().id() == ID_pointer, "this parameter must be a pointer");
  INVARIANT(
    this_expr.type().subtype() != empty_typet(),
    "this parameter must not be a void pointer");

  // So long as `this` is already not `void*` typed, the second parameter
  // is ignored:
  exprt this_class_identifier =
    get_class_identifier_field(this_expr, struct_tag_typet(irep_idt()), ns);

  // If instructed, add an ASSUME(FALSE) to handle the case where we don't
  // match any expected type:
  if(fallback_action==virtual_dispatch_fallback_actiont::ASSUME_FALSE)
  {
    new_code_calls.add(
      goto_programt::make_assumption(false_exprt(), vcall_source_loc));
  }

  // get initial identifier for grouping
  INVARIANT(!functions.empty(), "Function dispatch table cannot be empty.");
  const auto &last_function_symbol = functions.back().symbol_expr;

  std::map<irep_idt, goto_programt::targett> calls;
  // Note backwards iteration, to get the fallback candidate first.
  for(auto it=functions.crbegin(), itend=functions.crend(); it!=itend; ++it)
  {
    const auto &fun=*it;
    irep_idt id_or_empty = fun.symbol_expr.has_value()
                             ? fun.symbol_expr->get_identifier()
                             : irep_idt();
    auto insertit = calls.insert({id_or_empty, goto_programt::targett()});

    // Only create one call sequence per possible target:
    if(insertit.second)
    {
      if(fun.symbol_expr.has_value())
      {
        // call function
        auto new_call = code;

        create_static_function_call(new_call, *fun.symbol_expr, ns);

        goto_programt::targett t1 = new_code_calls.add(
          goto_programt::make_function_call(new_call, vcall_source_loc));

        insertit.first->second = t1;
      }
      else
      {
        goto_programt::targett t1 = new_code_calls.add(
          goto_programt::make_assertion(false_exprt(), vcall_source_loc));

        // No definition for this type; shouldn't be possible...
        t1->source_location_nonconst().set_comment(
          "cannot find calls for " +
          id2string(code.function().get(ID_identifier)) + " dispatching " +
          id2string(fun.class_id));

        insertit.first->second = t1;
      }

      // goto final
      new_code_calls.add(
        goto_programt::make_goto(t_final, true_exprt(), vcall_source_loc));
    }

    // Fall through to the default callee if possible:
    if(
      fallback_action ==
        virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION &&
      fun.symbol_expr.has_value() == last_function_symbol.has_value() &&
      (!fun.symbol_expr.has_value() ||
       *fun.symbol_expr == *last_function_symbol))
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
      if(
        it != functions.crbegin() &&
        std::prev(it)->symbol_expr.has_value() == fun.symbol_expr.has_value() &&
        (!fun.symbol_expr.has_value() ||
         *(std::prev(it)->symbol_expr) == *fun.symbol_expr))
      {
        INVARIANT(
          !new_code_gotos.empty(),
          "a dispatch table entry has been processed already, "
          "which should have created a GOTO");
        new_code_gotos.instructions.back().condition_nonconst() = or_exprt(
          new_code_gotos.instructions.back().condition(), class_id_test);
      }
      else
      {
        new_code_gotos.add(goto_programt::make_goto(
          insertit.first->second, class_id_test, vcall_source_loc));
      }
    }
  }

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_for_this_argument);
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  // set locations
  for(auto &instruction : new_code.instructions)
  {
    source_locationt &source_location = instruction.source_location_nonconst();

    const irep_idt property_class = source_location.get_property_class();
    const irep_idt comment = source_location.get_comment();
    source_location = target->source_location();
    if(!property_class.empty())
      source_location.set_property_class(property_class);
    if(!comment.empty())
      source_location.set_comment(comment);
  }

  goto_program.destructive_insert(next_target, new_code);

  // finally, kill original invocation
  target->turn_into_skip();

  // only remove skips within the virtual-function handling block
  remove_skip(goto_program, target, next_target);

  return next_target;
}

/// Replace specified virtual function call with a static call to its
/// most derived implementation
/// \param function_id: The identifier of the function we are currently
///   analysing
/// \param [in,out] goto_program: GOTO program to modify
/// \param target: iterator to a function in the supplied GOTO program
///   to replace. Must point to a virtual function call.
/// \return Returns a pointer to the statement in the supplied GOTO
///   program after replaced function call
goto_programt::targett remove_virtual_functionst::remove_virtual_function(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const exprt &function = as_const(*target).call_function();
  INVARIANT(
    can_cast_expr<class_method_descriptor_exprt>(function),
    "remove_virtual_function must take a function call instruction whose "
    "function is a class method descriptor ");
  INVARIANT(
    !as_const(*target).call_arguments().empty(),
    "virtual function calls must have at least a this-argument");

  get_virtual_calleest get_callees(symbol_table, class_hierarchy);
  dispatch_table_entriest functions;
  get_callees.get_functions(function, functions);

  return replace_virtual_function_with_dispatch_table(
    symbol_table,
    function_id,
    goto_program,
    target,
    functions,
    virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION);
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
void get_virtual_calleest::get_child_functions_rec(
  const irep_idt &this_id,
  const optionalt<symbol_exprt> &last_method_defn,
  const irep_idt &component_name,
  dispatch_table_entriest &functions,
  dispatch_table_entries_mapt &entry_map) const
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
      (!it->second.symbol_expr.has_value() ||
       !has_prefix(
         id2string(it->second.symbol_expr->get_identifier()),
         "java::java.lang.Object")))
    {
      continue;
    }
    exprt method = get_method(child, component_name);
    dispatch_table_entryt function(child);
    if(method.is_not_nil())
    {
      function.symbol_expr=to_symbol_expr(method);
      function.symbol_expr->set(ID_C_class, child);
    }
    else
    {
      function.symbol_expr=last_method_defn;
    }
    if(!function.symbol_expr.has_value())
    {
      const auto resolved_call = get_inherited_method_implementation(
        component_name, child, symbol_table);
      if(resolved_call)
      {
        function.class_id = resolved_call->get_class_identifier();
        const symbolt &called_symbol = symbol_table.lookup_ref(
          resolved_call->get_full_component_identifier());

        function.symbol_expr = called_symbol.symbol_expr();
        function.symbol_expr->set(
          ID_C_class, resolved_call->get_class_identifier());
      }
    }
    functions.push_back(function);
    entry_map.emplace(child, function);

    get_child_functions_rec(
      child, function.symbol_expr, component_name, functions, entry_map);
  }
}

/// Used to get dispatch entries to call for the given function
/// \param function: function that should be called
/// \param [out] functions: is assigned a list of dispatch entries, i.e., pairs
///   of class names and function symbol to call when encountering the class.
void get_virtual_calleest::get_functions(
  const exprt &function,
  dispatch_table_entriest &functions) const
{
  // class part of function to call
  const irep_idt class_id=function.get(ID_C_class);
  const std::string class_id_string(id2string(class_id));
  const irep_idt function_name = function.get(ID_component_name);
  const std::string function_name_string(id2string(function_name));
  INVARIANT(!class_id.empty(), "All virtual functions must have a class");

  auto resolved_call =
    get_inherited_method_implementation(function_name, class_id, symbol_table);

  // might be an abstract function
  dispatch_table_entryt root_function(class_id);

  if(resolved_call)
  {
    root_function.class_id = resolved_call->get_class_identifier();

    const symbolt &called_symbol =
      symbol_table.lookup_ref(resolved_call->get_full_component_identifier());

    root_function.symbol_expr=called_symbol.symbol_expr();
    root_function.symbol_expr->set(
      ID_C_class, resolved_call->get_class_identifier());
  }

  // iterate over all children, transitively
  dispatch_table_entries_mapt entry_map;
  get_child_functions_rec(
    class_id, root_function.symbol_expr, function_name, functions, entry_map);

  if(root_function.symbol_expr.has_value())
    functions.push_back(root_function);

  // Sort for the identifier of the function call symbol expression, grouping
  // together calls to the same function. Keep java.lang.Object entries at the
  // end for fall through. The reasoning is that this is the case with most
  // entries in realistic cases.
  std::sort(
    functions.begin(),
    functions.end(),
    [](const dispatch_table_entryt &a, const dispatch_table_entryt &b) {
      irep_idt a_id = a.symbol_expr.has_value()
                        ? a.symbol_expr->get_identifier()
                        : irep_idt();
      irep_idt b_id = b.symbol_expr.has_value()
                        ? b.symbol_expr->get_identifier()
                        : irep_idt();

      if(has_prefix(id2string(a_id), "java::java.lang.Object"))
        return false;
      else if(has_prefix(id2string(b_id), "java::java.lang.Object"))
        return true;
      else
      {
        int cmp = a_id.compare(b_id);
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
///   the method on success
exprt get_virtual_calleest::get_method(
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
  const irep_idt &function_id,
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
      if(can_cast_expr<class_method_descriptor_exprt>(
           as_const(*target).call_function()))
      {
        target = remove_virtual_function(function_id, goto_program, target);
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
    const irep_idt &function_id = f_it->first;
    goto_programt &goto_program=f_it->second.body;

    if(remove_virtual_functions(function_id, goto_program))
      did_something=true;
  }

  if(did_something)
    functions.compute_location_numbers();
}

/// Remove virtual function calls from all functions in the specified
/// list and replace them with their most derived implementations
/// \param symbol_table: symbol table associated with \p goto_functions
/// \param goto_functions: functions from which to remove virtual function calls
void remove_virtual_functions(
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions)
{
  class_hierarchyt class_hierarchy;
  class_hierarchy(symbol_table);
  remove_virtual_functionst rvf(symbol_table, class_hierarchy);
  rvf(goto_functions);
}

/// Remove virtual function calls from all functions in the specified
/// list and replace them with their most derived implementations
/// \param symbol_table: symbol table associated with \p goto_functions
/// \param goto_functions: functions from which to remove virtual function calls
/// \param class_hierarchy: class hierarchy derived from symbol_table
///   This should already be populated (i.e. class_hierarchyt::operator() has
///   already been called)
void remove_virtual_functions(
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions,
  const class_hierarchyt &class_hierarchy)
{
  remove_virtual_functionst rvf(symbol_table, class_hierarchy);
  rvf(goto_functions);
}

/// Remove virtual function calls from the specified model
/// \param goto_model: model from which to remove virtual functions
void remove_virtual_functions(goto_modelt &goto_model)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions);
}

/// Remove virtual function calls from the specified model
/// \param goto_model: model from which to remove virtual functions
/// \param class_hierarchy: class hierarchy derived from model.symbol_table
///   This should already be populated (i.e. class_hierarchyt::operator() has
///   already been called)
void remove_virtual_functions(
  goto_modelt &goto_model,
  const class_hierarchyt &class_hierarchy)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions, class_hierarchy);
}

/// Remove virtual function calls from the specified model function
/// May change the location numbers in `function`.
/// \param function: function from which virtual functions should be converted
///   to explicit dispatch tables.
void remove_virtual_functions(goto_model_functiont &function)
{
  class_hierarchyt class_hierarchy;
  class_hierarchy(function.get_symbol_table());
  remove_virtual_functionst rvf(function.get_symbol_table(), class_hierarchy);
  rvf.remove_virtual_functions(
    function.get_function_id(), function.get_goto_function().body);
}

/// Remove virtual function calls from the specified model function
/// May change the location numbers in `function`.
/// \param function: function from which virtual functions should be converted
///   to explicit dispatch tables.
/// \param class_hierarchy: class hierarchy derived from function.symbol_table
///   This should already be populated (i.e. class_hierarchyt::operator() has
///   already been called)
void remove_virtual_functions(
  goto_model_functiont &function,
  const class_hierarchyt &class_hierarchy)
{
  remove_virtual_functionst rvf(function.get_symbol_table(), class_hierarchy);
  rvf.remove_virtual_functions(
    function.get_function_id(), function.get_goto_function().body);
}

/// Replace virtual function call with a static function call
/// Achieved by substituting a virtual function with its most derived
/// implementation. If there's a type mismatch between implementation
/// and the instance type or if fallback_action is set to
/// ASSUME_FALSE, then function is substituted with a call to ASSUME(false)
/// \param symbol_table: Symbol table
/// \param function_id: The identifier of the function we are currently
///   analysing
/// \param [in,out] goto_program: GOTO program to modify
/// \param instruction: Iterator to the GOTO instruction in the supplied
///   GOTO program to be removed. Must point to a function call
/// \param dispatch_table: Dispatch table - all possible implementations of
///   this function sorted from the least to the most derived
/// \param fallback_action: - ASSUME_FALSE to replace virtual function
///   calls with ASSUME(false) or CALL_LAST_FUNCTION to replace them
///   with the most derived matching call
/// \return Returns a pointer to the statement in the supplied GOTO
///   program after replaced function call
goto_programt::targett remove_virtual_function(
  symbol_tablet &symbol_table,
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action)
{
  goto_programt::targett next = replace_virtual_function_with_dispatch_table(
    symbol_table,
    function_id,
    goto_program,
    instruction,
    dispatch_table,
    fallback_action);

  goto_program.update();

  return next;
}

goto_programt::targett remove_virtual_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action)
{
  return remove_virtual_function(
    goto_model.symbol_table,
    function_id,
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
  get_virtual_calleest get_callees(symbol_table, class_hierarchy);
  get_callees.get_functions(function, overridden_functions);
}
