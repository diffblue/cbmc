/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Remove Virtual Function (Method) Calls

#include <util/prefix.h>
#include <util/type_eq.h>

#include "class_hierarchy.h"
#include "class_identifier.h"
#include "remove_virtual_functions.h"

class remove_virtual_functionst
{
public:
  remove_virtual_functionst(
    const symbol_tablet &_symbol_table,
    const goto_functionst &goto_functions);

  void operator()(goto_functionst &goto_functions);

  bool remove_virtual_functions(goto_programt &goto_program);

protected:
  const namespacet ns;
  const symbol_tablet &symbol_table;

  class_hierarchyt class_hierarchy;

  void remove_virtual_function(
    goto_programt &goto_program,
    goto_programt::targett target);

  class functiont
  {
  public:
    functiont() {}
    explicit functiont(const irep_idt &_class_id) :
      class_id(_class_id)
    {}

    symbol_exprt symbol_expr;
    irep_idt class_id;
  };

  using functionst = std::vector<functiont>;
  void get_functions(const exprt &, functionst &);
  void get_child_functions_rec(
    const irep_idt &,
    const symbol_exprt &,
    const irep_idt &,
    functionst &,
    std::set<irep_idt> &visited) const;
  exprt get_method(
    const irep_idt &class_id,
    const irep_idt &component_name) const;
};

remove_virtual_functionst::remove_virtual_functionst(
  const symbol_tablet &_symbol_table,
  const goto_functionst &goto_functions):
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

  const auto &vcall_source_loc=target->source_location;

  const exprt &function=code.function();
  assert(function.id()==ID_virtual_function);
  assert(!code.arguments().empty());

  functionst functions;
  get_functions(function, functions);

  if(functions.empty())
  {
    target->make_skip();
    return; // give up
  }

  // only one option?
  if(functions.size()==1)
  {
    assert(target->is_function_call());
    if(functions.begin()->symbol_expr==symbol_exprt())
      target->make_skip();
    else
      to_code_function_call(target->code).function()=
        functions.begin()->symbol_expr;
    return;
  }

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final=final_skip.add_instruction();
  t_final->source_location=vcall_source_loc;

  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  exprt this_expr=code.arguments()[0];
  // If necessary, cast to the last candidate function to
  // get the object's clsid. By the structure of get_functions,
  // this is the parent of all other classes under consideration.
  const auto &base_classid=functions.back().class_id;
  const auto &base_function_symbol=functions.back().symbol_expr;
  symbol_typet suggested_type(base_classid);
  exprt c_id2=get_class_identifier_field(this_expr, suggested_type, ns);

  std::map<irep_idt, goto_programt::targett> calls;
  // Note backwards iteration, to get the least-derived candidate first.
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
        auto &newcall=to_code_function_call(t1->code);
        newcall.function()=fun.symbol_expr;
        pointer_typet need_type(symbol_typet(fun.symbol_expr.get(ID_C_class)));
        if(!type_eq(newcall.arguments()[0].type(), need_type, ns))
          newcall.arguments()[0].make_typecast(need_type);
      }
      else
      {
        // No definition for this type; shouldn't be possible...
        t1->make_assertion(false_exprt());
      }
      insertit.first->second=t1;
      // goto final
      goto_programt::targett t3=new_code_calls.add_instruction();
      t3->source_location=vcall_source_loc;
      t3->make_goto(t_final, true_exprt());
    }

    // If this calls the base function we just fall through.
    // Otherwise branch to the right call:
    if(fun.symbol_expr!=base_function_symbol)
    {
      exprt c_id1=constant_exprt(fun.class_id, string_typet());
      goto_programt::targett t4=new_code_gotos.add_instruction();
      t4->source_location=vcall_source_loc;
      t4->make_goto(insertit.first->second, equal_exprt(c_id1, c_id2));
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
/// \return `functions` is assigned a list of {class name, function symbol}
///   pairs indicating that if `this` is of the given class, then the call will
///   target the given function. Thus if A <: B <: C and A and C provide
///   overrides of `f` (but B does not), get_child_functions_rec("C", C.f, "f")
///   -> [{"C", C.f}, {"B", C.f}, {"A", A.f}]
void remove_virtual_functionst::get_child_functions_rec(
  const irep_idt &this_id,
  const symbol_exprt &last_method_defn,
  const irep_idt &component_name,
  functionst &functions,
  std::set<irep_idt> &visited) const
{
  auto findit=class_hierarchy.class_map.find(this_id);
  if(findit==class_hierarchy.class_map.end())
    return;

  for(const auto &child : findit->second.children)
  {
    if(!visited.insert(child).second)
      continue;
    exprt method=get_method(child, component_name);
    functiont function(child);
    if(method.is_not_nil())
    {
      function.symbol_expr=to_symbol_expr(method);
      function.symbol_expr.set(ID_C_class, child);
    }
    else
    {
      function.symbol_expr=last_method_defn;
    }
    functions.push_back(function);

    get_child_functions_rec(
      child,
      function.symbol_expr,
      component_name,
      functions,
      visited);
  }
}

void remove_virtual_functionst::get_functions(
  const exprt &function,
  functionst &functions)
{
  const irep_idt class_id=function.get(ID_C_class);
  const irep_idt component_name=function.get(ID_component_name);
  assert(!class_id.empty());
  functiont root_function;

  // Start from current class, go to parents until something
  // is found.
  irep_idt c=class_id;
  while(!c.empty())
  {
    exprt method=get_method(c, component_name);
    if(method.is_not_nil())
    {
      root_function.class_id=c;
      root_function.symbol_expr=to_symbol_expr(method);
      root_function.symbol_expr.set(ID_C_class, c);
      break; // abort
    }

    const class_hierarchyt::idst &parents=
      class_hierarchy.class_map[c].parents;

    if(parents.empty())
      break;
    c=parents.front();
  }

  if(root_function.class_id.empty())
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
    visited);

  if(root_function.symbol_expr!=symbol_exprt())
    functions.push_back(root_function);
}

exprt remove_virtual_functionst::get_method(
  const irep_idt &class_id,
  const irep_idt &component_name) const
{
  irep_idt id=id2string(class_id)+"."+
              id2string(component_name);

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
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_virtual_functionst
    rvf(symbol_table, goto_functions);

  rvf(goto_functions);
}

void remove_virtual_functions(goto_modelt &goto_model)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions);
}
