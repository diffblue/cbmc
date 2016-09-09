/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/prefix.h>

#include "class_hierarchy.h"
#include "remove_virtual_functions.h"

/*******************************************************************\

   Class: remove_virtual_functionst

 Purpose:

\*******************************************************************/

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
    symbol_exprt symbol_expr;
    irep_idt class_id;
  };

  typedef std::vector<functiont> functionst;
  void get_functions(const exprt &, functionst &);
  void get_child_functions_rec(const irep_idt &, const symbol_exprt &,
                               const irep_idt &, functionst &);
  exprt get_method(const irep_idt &class_id, const irep_idt &component_name);

  exprt build_class_identifier(const exprt &);
};

/*******************************************************************\

Function: remove_virtual_functionst::remove_virtual_functionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

remove_virtual_functionst::remove_virtual_functionst(
  const symbol_tablet &_symbol_table,
  const goto_functionst &goto_functions):
  ns(_symbol_table),
  symbol_table(_symbol_table)
{
  class_hierarchy(symbol_table);
}

/*******************************************************************\

Function: remove_virtual_functionst::build_class_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt remove_virtual_functionst::build_class_identifier(
  const exprt &src)
{
  // the class identifier is in the root class
  exprt e=src;

  while(1)
  {
    const typet &type=ns.follow(e.type());
    assert(type.id()==ID_struct);

    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    assert(!components.empty());

    member_exprt member_expr(
      e, components.front().get_name(), components.front().type());

    if(components.front().get_name()=="@class_identifier")
    {
      // found it
      return member_expr;
    }
    else
    {
      e=member_expr;
    }
  }
}

/*******************************************************************\

Function: remove_virtual_functionst::remove_virtual_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_virtual_functionst::remove_virtual_function(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &code=
    to_code_function_call(target->code);

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
    to_code_function_call(target->code).function()=
      functions.begin()->symbol_expr;

    return;
  }

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final=final_skip.add_instruction();
  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  // Get a pointer from which we can extract a clsid.
  // If it's already a pointer to an object of some sort, just use it;
  // if it's void* then use the parent of all possible candidates,
  // which by the nature of get_functions happens to be the last candidate.

  exprt this_expr=code.arguments()[0];
  assert(this_expr.type().id()==ID_pointer &&
         "Non-pointer this-arg in remove-virtuals?");
  const auto& points_to=this_expr.type().subtype();
  if(points_to==empty_typet())
  {
    symbol_typet symbol_type(functions.back().class_id);
    this_expr=typecast_exprt(this_expr, pointer_typet(symbol_type));
  }
  exprt deref=dereference_exprt(this_expr, this_expr.type().subtype());
  exprt c_id2=build_class_identifier(deref);

  for(const auto &fun : functions)
  {
    goto_programt::targett t1=new_code_calls.add_instruction();
    if(fun.symbol_expr.get_identifier()!=irep_idt())
    {
      // call function
      t1->make_function_call(code);
      auto& newcall=to_code_function_call(t1->code);
      newcall.function()=fun.symbol_expr;
      pointer_typet need_type(symbol_typet(fun.symbol_expr.get(ID_C_class)));
      if(newcall.arguments()[0].type()!=need_type)
        newcall.arguments()[0].make_typecast(need_type);
    }
    else
    {
      // No definition for this type; shouldn't be possible...
      t1->make_assertion(false_exprt());
    }

    // goto final
    goto_programt::targett t3=new_code_calls.add_instruction();
    t3->make_goto(t_final, true_exprt());

    exprt c_id1=constant_exprt(fun.class_id, string_typet());

    goto_programt::targett t4=new_code_gotos.add_instruction();
    t4->make_goto(t1, equal_exprt(c_id1, c_id2));
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
    if(!property_class.empty()) it->source_location.set_property_class(property_class);
    if(!comment.empty()) it->source_location.set_comment(comment);
  }

  goto_programt::targett next_target=target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // finally, kill original invocation
  target->make_skip();
}

void remove_virtual_functionst::get_child_functions_rec(
  const irep_idt &this_id,
  const symbol_exprt &last_method_defn,
  const irep_idt &component_name,
  functionst &functions)
{
  auto findit=class_hierarchy.class_map.find(this_id);
  if(findit==class_hierarchy.class_map.end())
    return;

  for(const auto & child : findit->second.children)
  {
    exprt method=get_method(child, component_name);
    functiont function;
    function.class_id=child;
    if(method.is_not_nil())
    {
      function.symbol_expr=to_symbol_expr(method);
      function.symbol_expr.set(ID_C_class, child);
    }
    else {
      function.symbol_expr=last_method_defn;
    }
    functions.push_back(function);

    get_child_functions_rec(child,function.symbol_expr,component_name,functions);
  }
}

/*******************************************************************\

Function: remove_virtual_functionst::get_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

    if(parents.empty()) break;
    c=parents.front();
  }

  if(root_function.class_id==irep_idt())
  {
    // No definition here; this is an abstract function.
    root_function.class_id=class_id;
  }

  // iterate over all children, transitively
  get_child_functions_rec(class_id,root_function.symbol_expr,component_name,functions);

  functions.push_back(root_function);

}

/*******************************************************************\

Function: remove_virtual_functionst::get_method

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt remove_virtual_functionst::get_method(
  const irep_idt &class_id,
  const irep_idt &component_name)
{
  irep_idt id=id2string(class_id)+"."+
              id2string(component_name);

  const symbolt *symbol;
  if(ns.lookup(id, symbol))
    return nil_exprt();

  return symbol->symbol_expr();
}

/*******************************************************************\

Function: remove_virtual_functionst::remove_virtual_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    //remove_skip(goto_program);
    goto_program.update();
  }

  return did_something;
}

/*******************************************************************\

Function: remove_virtual_functionst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: remove_virtual_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_virtual_functions(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_virtual_functionst
    rvf(symbol_table, goto_functions);

  rvf(goto_functions);
}

/*******************************************************************\

Function: remove_virtual_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_virtual_functions(goto_modelt &goto_model)
{
  remove_virtual_functions(
    goto_model.symbol_table, goto_model.goto_functions);
}
