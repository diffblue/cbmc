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
    std::set<irep_idt> &visited,
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

  // Filter out function for which the type is not loaded
  dispatch_table_entriest filtered_functions;
  for(const dispatch_table_entryt &fun : functions)
  {
    const constant_exprt class_id(fun.class_id, string_typet());
    if(fun.symbol_expr.get_identifier().empty())
    {
      goto_programt::targett target_for_assertion =
        new_code_calls.add_instruction();
      target_for_assertion->source_location = vcall_source_loc;

      // No definition for this type, assume this is not the current type
      target_for_assertion->make_assertion(notequal_exprt(class_id, c_id2));
      target_for_assertion->source_location.set_comment(
        ("cannot find calls for " +
         id2string(code.function().get(ID_identifier)) + " dispatching " +
         id2string(fun.class_id)));
    }
    else
      filtered_functions.push_back(fun);
  }

  std::map<irep_idt, goto_programt::targett> calls;
  const auto &last_function_symbol = filtered_functions.back().symbol_expr;
  // Note backwards iteration, to get the fallback candidate first.
  for(auto it = filtered_functions.crbegin(),
           itend = filtered_functions.crend();
      it != itend;
      ++it)
  {
    const auto &fun=*it;

    auto insertit=calls.insert(
      {fun.symbol_expr.get_identifier(), goto_programt::targett()});

    // Only create one call sequence per possible target:
    if(insertit.second)
    {
      goto_programt::targett target_for_call = new_code_calls.add_instruction();
      target_for_call->source_location = vcall_source_loc;

      // call function
      target_for_call->make_function_call(code);
      auto &newcall = to_code_function_call(target_for_call->code);
      newcall.function() = fun.symbol_expr;
      // Cast the `this` pointer to the correct type for the new callee:
      const auto &callee_type =
        to_code_type(ns.lookup(fun.symbol_expr.get_identifier()).type);
      const code_typet::parametert *this_param = callee_type.get_this();
      INVARIANT(
        this_param != nullptr,
        "Virtual function callees must have a `this` argument");
      typet need_type = this_param->type();
      if(!type_eq(newcall.arguments()[0].type(), need_type, ns))
        newcall.arguments()[0].make_typecast(need_type);

      insertit.first->second = target_for_call;
      // goto final
      goto_programt::targett target_for_goto = new_code_calls.add_instruction();
      target_for_goto->source_location = vcall_source_loc;
      target_for_goto->make_goto(t_final, true_exprt());
    }

    // If this calls the fallback function we just fall through.
    // Otherwise branch to the right call:
    if(fallback_action!=virtual_dispatch_fallback_actiont::CALL_LAST_FUNCTION ||
       fun.symbol_expr!=last_function_symbol)
    {
      const constant_exprt c_id1(fun.class_id, string_typet());
      goto_programt::targett target_for_goto_condition =
        new_code_gotos.add_instruction();
      target_for_goto_condition->source_location = vcall_source_loc;
      target_for_goto_condition->make_goto(
        insertit.first->second, equal_exprt(c_id1, c_id2));
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
/// \par parameters: `this_id`: class name
/// `last_method_defn`: the most-derived parent of `this_id` to define the
///   requested function
/// `component_name`: name of the function searched for
/// `resolve_function_call`: function to resolve abstract method call
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
  std::set<irep_idt> &visited,
  const function_call_resolvert &resolve_function_call) const
{
  auto findit=class_hierarchy.class_map.find(this_id);
  if(findit==class_hierarchy.class_map.end())
    return;

  for(const auto &child : findit->second.children)
  {
    if(!visited.insert(child).second)
      continue;
    exprt method=get_method(child, component_name);
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

    get_child_functions_rec(
      child,
      function.symbol_expr,
      component_name,
      functions,
      visited,
      resolve_function_call);
  }
}

void remove_virtual_functionst::get_functions(
  const exprt &function,
  dispatch_table_entriest &functions)
{
  const irep_idt class_id=function.get(ID_C_class);
  const std::string class_id_string(id2string(class_id));
  const irep_idt component_name=function.get(ID_component_name);
  const std::string component_name_string(id2string(component_name));
  INVARIANT(!class_id.empty(), "All virtual functions must have a class");

  resolve_concrete_function_callt get_virtual_call_target(
    symbol_table, class_hierarchy);
  const function_call_resolvert resolve_function_call =
    [&get_virtual_call_target](
      const irep_idt &class_id, const irep_idt &component_name) {
      return get_virtual_call_target(class_id, component_name);
    };

  const resolve_concrete_function_callt::concrete_function_callt
    &resolved_call = get_virtual_call_target(class_id, component_name);

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
  std::set<irep_idt> visited;
  get_child_functions_rec(
    class_id,
    root_function.symbol_expr,
    component_name,
    functions,
    visited,
    resolve_function_call);

  if(root_function.symbol_expr!=symbol_exprt())
    functions.push_back(root_function);
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
