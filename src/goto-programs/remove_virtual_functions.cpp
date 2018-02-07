/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Remove Virtual Function (Method) Calls
#include <algorithm>

#include "remove_virtual_functions.h"
#include "class_hierarchy.h"
#include "class_identifier.h"

#include <goto-programs/resolve_concrete_function_call.h>

#include <util/c_types.h>
#include <util/prefix.h>
#include <util/type_eq.h>

class remove_virtual_functionst
{
public:
  remove_virtual_functionst(
    const symbol_table_baset &_symbol_table);

  void operator()(goto_functionst &goto_functions);

  bool remove_virtual_functions(goto_programt &goto_program);

  void remove_virtual_function(
    goto_programt &goto_program,
    goto_programt::targett target,
    const dispatch_table_entriest &functions,
    virtual_dispatch_fallback_actiont fallback_action);

protected:
  const namespacet ns;
  const symbol_table_baset &symbol_table;

  class_hierarchyt class_hierarchy;

  void remove_virtual_function(
    goto_programt &goto_program,
    goto_programt::targett target);

  void get_functions(const exprt &, dispatch_table_entriest &);
  typedef std::function<
    resolve_concrete_function_callt::concrete_function_callt(
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
  const symbol_table_baset &_symbol_table):
  ns(_symbol_table),
  symbol_table(_symbol_table)
{
  class_hierarchy(symbol_table);
}

void remove_virtual_functionst::remove_virtual_function(
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

  remove_virtual_function(
    goto_program,
    target,
    functions,
    virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION);
}

void remove_virtual_functionst::remove_virtual_function(
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

  if(functions.empty())
  {
    target->make_skip();
    return; // give up
  }

  // only one option?
  if(functions.size()==1 &&
     fallback_action==virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION)
  {
    if(functions.begin()->symbol_expr==symbol_exprt())
      target->make_skip();
    else
      to_code_function_call(target->code).function()=
        functions.begin()->symbol_expr;
    return;
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
  exprt c_id2=get_class_identifier_field(this_expr, symbol_typet(), ns);

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
  auto last_id = functions.back().symbol_expr.get_identifier();
  // record class_ids for disjunction
  std::set<irep_idt> class_ids;

  std::map<irep_idt, goto_programt::targett> calls;
  // Note backwards iteration, to get the fallback candidate first.
  for(auto it=functions.crbegin(), itend=functions.crend(); it!=itend; ++it)
  {
    const auto &fun=*it;
    class_ids.insert(fun.class_id);
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
        auto &newcall=to_code_function_call(t1->code);
        newcall.function()=fun.symbol_expr;
        // Cast the `this` pointer to the correct type for the new callee:
        const auto &callee_type=
          to_code_type(ns.lookup(fun.symbol_expr.get_identifier()).type);
        const code_typet::parametert *this_param = callee_type.get_this();
        INVARIANT(
          this_param != nullptr,
          "Virtual function callees must have a `this` argument");
        typet need_type=this_param->type();
        if(!type_eq(newcall.arguments()[0].type(), need_type, ns))
          newcall.arguments()[0].make_typecast(need_type);
      }
      else
      {
        // No definition for this type; shouldn't be possible...
        t1->make_assertion(false_exprt());
        t1->source_location.set_comment(
          ("cannot find calls for " +
           id2string(code.function().get(ID_identifier)) + " dispatching " +
           id2string(fun.class_id)));
      }
      insertit.first->second=t1;
      // goto final
      goto_programt::targett t3=new_code_calls.add_instruction();
      t3->source_location=vcall_source_loc;
      t3->make_goto(t_final, true_exprt());
    }

    // Emit target if end of dispatch table is reached or if the next element is
    // dispatched to another function call. Assumes entries in the functions
    // variable to be sorted for the identifier of the function to be called.
    auto l_it = std::next(it);
    bool next_emit_target =
      (l_it == functions.crend()) ||
      l_it->symbol_expr.get_identifier() != fun.symbol_expr.get_identifier();

    // The root function call is done via fall-through, so nothing to emit
    // explicitly for this.
    if(next_emit_target && fun.symbol_expr == last_function_symbol)
    {
      class_ids.clear();
    }

    // If this calls the fallback function we just fall through.
    // Otherwise branch to the right call:
    if(fallback_action!=virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION ||
       fun.symbol_expr!=last_function_symbol)
    {
      // create a disjunction of class_ids to test
      if(next_emit_target && fun.symbol_expr != last_function_symbol)
      {
        exprt::operandst or_ops;
        for(const auto &id : class_ids)
        {
          const constant_exprt c_id1(id, string_typet());
          const equal_exprt class_id_test(c_id1, c_id2);
          or_ops.push_back(class_id_test);
        }

        goto_programt::targett t4 = new_code_gotos.add_instruction();
        t4->source_location = vcall_source_loc;
        t4->make_goto(insertit.first->second, disjunction(or_ops));

        last_id = fun.symbol_expr.get_identifier();
        class_ids.clear();
      }
      // record class_id
      else if(next_emit_target)
      {
        last_id = fun.symbol_expr.get_identifier();
        class_ids.clear();
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

  goto_programt::targett next_target=target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // finally, kill original invocation
  target->make_skip();
}

/// Used by get_functions to track the most-derived parent that provides an
/// override of a given function.
/// \param parameters: `this_id`: class name
/// \param `last_method_defn`: the most-derived parent of `this_id` to define
///   the requested function
/// \param `component_name`: name of the function searched for
/// \param `entry_map`: map of class identifiers to dispatch table entries
/// \param `resolve_function_call`: function to resolve abstract method call
/// \return `functions` is assigned a list of {class name, function symbol}
///   pairs indicating that if `this` is of the given class, then the call will
///   target the given function. Thus if A <: B <: C and A and C provide
///   overrides of `f` (but B does not), get_child_functions_rec("C", C.f, "f")
///   -> [{"C", C.f}, {"B", C.f}, {"A", A.f}]
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
      const resolve_concrete_function_callt::concrete_function_callt
        &resolved_call = resolve_function_call(child, component_name);
      if(resolved_call.is_valid())
      {
        function.class_id = resolved_call.get_class_identifier();
        const symbolt &called_symbol =
          symbol_table.lookup_ref(resolved_call.get_virtual_method_name());

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
/// \param[out] functions: is assigned a list of dispatch entries, i.e., pairs
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

  resolve_concrete_function_callt get_virtual_call_target(
    symbol_table, class_hierarchy);
  const function_call_resolvert resolve_function_call =
    [&get_virtual_call_target](
      const irep_idt &class_id, const irep_idt &function_name) {
      return get_virtual_call_target(class_id, function_name);
    };

  const resolve_concrete_function_callt::concrete_function_callt
    &resolved_call = get_virtual_call_target(class_id, function_name);

  dispatch_table_entryt root_function;

  if(resolved_call.is_valid())
  {
    root_function.class_id=resolved_call.get_class_identifier();

    const symbolt &called_symbol =
      symbol_table.lookup_ref(resolved_call.get_virtual_method_name());

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
    [&root_function](const dispatch_table_entryt &a, dispatch_table_entryt &b) {
      if(
        has_prefix(
          id2string(a.symbol_expr.get_identifier()), "java::java.lang.Object"))
        return false;
      else if(
        has_prefix(
          id2string(b.symbol_expr.get_identifier()), "java::java.lang.Object"))
        return true;
      else
        return a.symbol_expr.get_identifier() < b.symbol_expr.get_identifier();
    });
}

exprt remove_virtual_functionst::get_method(
  const irep_idt &class_id,
  const irep_idt &component_name) const
{
  const irep_idt &id=
    resolve_concrete_function_callt::build_virtual_method_name(
      class_id, component_name);

  const symbolt *symbol;
  if(ns.lookup(id, symbol))
    return nil_exprt();

  return symbol->symbol_expr();
}

bool remove_virtual_functionst::remove_virtual_functions(
  goto_programt &goto_program)
{
  bool did_something=false;

  Forall_goto_program_instructions(target, goto_program)
    if(target->is_function_call())
    {
      const code_function_callt &code=
        to_code_function_call(target->code);

      if(code.function().id()==ID_virtual_function)
      {
        remove_virtual_function(goto_program, target);
        did_something=true;
      }
    }

  if(did_something)
  {
    goto_program.update();
  }

  return did_something;
}

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

void remove_virtual_functions(
  const symbol_table_baset &symbol_table,
  goto_functionst &goto_functions)
{
  remove_virtual_functionst rvf(symbol_table);
  rvf(goto_functions);
}

void remove_virtual_functions(goto_modelt &goto_model)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions);
}

void remove_virtual_functions(goto_model_functiont &function)
{
  remove_virtual_functionst rvf(function.get_symbol_table());
  bool changed = rvf.remove_virtual_functions(
    function.get_goto_function().body);
  // Give fresh location numbers to `function`, in case it has grown:
  if(changed)
    function.compute_location_numbers();
}

void remove_virtual_function(
  goto_modelt &goto_model,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action)
{
  remove_virtual_functionst rvf(goto_model.symbol_table);

  rvf.remove_virtual_function(
    goto_program, instruction, dispatch_table, fallback_action);
}
