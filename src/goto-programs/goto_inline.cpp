/*******************************************************************\

Module: Function Inlining

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <prefix.h>
#include <cprover_prefix.h>
#include <base_type.h>
#include <std_code.h>
#include <std_expr.h>
#include <expr_util.h>

#include "remove_skip.h"
#include "goto_inline.h"
#include "goto_inline_class.h"

/*******************************************************************\

Function: goto_inlinet::parameter_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::parameter_assignments(
  const locationt &location,
  const code_typet &code_type,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  // iterates over the operands
  exprt::operandst::const_iterator it1=arguments.begin();

  const code_typet::argumentst &argument_types=
    code_type.arguments();
  
  // iterates over the types of the arguments
  for(code_typet::argumentst::const_iterator
      it2=argument_types.begin();
      it2!=argument_types.end();
      it2++)
  {
    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      err_location(location);
      throw "function call: not enough arguments";
    }

    const code_typet::argumentt &argument=*it2;

    // this is the type the n-th argument should be
    const typet &arg_type=ns.follow(argument.type());

    const irep_idt &identifier=argument.get_identifier();

    if(identifier==irep_idt())
    {
      err_location(location);
      throw "no identifier for function argument";
    }

    {
      const symbolt &symbol=ns.lookup(identifier);

      goto_programt::targett decl=dest.add_instruction();
      decl->make_decl();
      decl->code=code_declt(symbol_expr(symbol));
      decl->code.location()=location;
      decl->location=location;
      decl->function=location.get_function(); 
    }

    // nil means "don't assign"
    if(it1->is_nil())
    {    
    }
    else
    {
      // this is the actual parameter
      exprt actual(*it1);

      // it should be the same exact type,
      // subject to some exceptions
      if(!base_type_eq(arg_type, actual.type(), ns))
      {
        const typet &f_argtype = ns.follow(arg_type);
        const typet &f_acttype = ns.follow(actual.type());
        
        // we are willing to do some conversion
        if((f_argtype.id()==ID_pointer &&
            f_acttype.id()==ID_pointer) ||
           (f_argtype.id()==ID_array &&
            f_acttype.id()==ID_pointer &&
            f_argtype.subtype()==f_acttype.subtype()))
        {
          actual.make_typecast(arg_type);
        }
        else if((f_argtype.id()==ID_signedbv ||
                 f_argtype.id()==ID_unsignedbv ||
                 f_argtype.id()==ID_bool) &&
                (f_acttype.id()==ID_signedbv ||
                 f_acttype.id()==ID_unsignedbv ||
                 f_acttype.id()==ID_bool))  
        {
          actual.make_typecast(arg_type);
        }
        else
        {
          err_location(*it1);

          str << "function call: argument `" << identifier
              << "' type mismatch: got `"
              << from_type(ns, identifier, it1->type())
              << "', expected `"
              << from_type(ns, identifier, arg_type)
              << "'";
          throw 0;
        }
      }

      // adds an assignment of the actual parameter to the formal parameter
      code_assignt assignment(symbol_exprt(identifier, arg_type), actual);
      assignment.location()=location;

      dest.add_instruction(ASSIGN);
      dest.instructions.back().location=location;
      dest.instructions.back().code.swap(assignment);
      dest.instructions.back().function=location.get_function();      
    }

    it1++;
  }

  if(it1!=arguments.end())
  {
    // too many arguments -- we just ignore that, no harm done
  }
}

/*******************************************************************\

Function: goto_inlinet::replace_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::replace_return(
  goto_programt &dest,
  const exprt &lhs,
  const exprt &constrain)
{
  for(goto_programt::instructionst::iterator
      it=dest.instructions.begin();
      it!=dest.instructions.end();
      it++)
  {
    if(it->is_return())
    {
      if(lhs.is_not_nil())
      {
        if(it->code.operands().size()!=1)
        {
          err_location(it->code);
          str << "return expects one operand!" << std::endl;
          warning();
	  continue;
        }
      
        goto_programt tmp;
        goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
        
        code_assignt code_assign(lhs, it->code.op0());

        // this may happen if the declared return type at the call site
        // differs from the defined return type
        if(code_assign.lhs().type()!=
           code_assign.rhs().type())
          code_assign.rhs().make_typecast(code_assign.lhs().type());

        assignment->code=code_assign;
        assignment->location=it->location;
        assignment->function=it->location.get_function();
        
        if(constrain.is_not_nil() && !constrain.is_true())
        {
          codet constrain(ID_bp_constrain);
          constrain.reserve_operands(2);
          constrain.move_to_operands(assignment->code);
          constrain.copy_to_operands(constrain);
        }
        
        dest.insert_before_swap(it, *assignment);
        it++;
      }
      else if(!it->code.operands().empty())
      {
        goto_programt tmp;
        goto_programt::targett expression=tmp.add_instruction(OTHER);
        
        expression->code=codet(ID_expression);
        expression->code.move_to_operands(it->code.op0());
        expression->location=it->location;
        expression->function=it->location.get_function();
        
        dest.insert_before_swap(it, *expression);
        it++;
      }

      it->make_goto(--dest.instructions.end());
    }
  }
}

/*******************************************************************\

Function: replace_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void replace_location(locationt &dest, const locationt &new_location)
{
  // can't just copy, e.g., due to comments field
  dest.id(irep_idt()); // not NIL
  dest.set_file(new_location.get_file());
  dest.set_line(new_location.get_line());
  dest.set_column(new_location.get_column());
  dest.set_function(new_location.get_function());
}

/*******************************************************************\

Function: replace_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void replace_location(exprt &dest, const locationt &new_location)
{
  Forall_operands(it, dest)
    replace_location(*it, new_location);

  if(dest.find(ID_C_location).is_not_nil())
    replace_location(dest.location(), new_location);
}

/*******************************************************************\

Function: goto_inlinet::expand_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::expand_function_call(
  goto_programt &dest,
  goto_programt::targett &target,
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  const exprt &constrain,
  bool full)
{
  // look it up
  if(function.id()!=ID_symbol)
  {
    err_location(function);
    throw "function_call expects symbol as function operand, "
          "but got `"+function.id_string()+"'";
  }
  
  const irep_idt &identifier=function.get(ID_identifier);
  
  // see if we are already expanding it
  if(recursion_set.find(identifier)!=recursion_set.end())
  {
    if(!full)
    {
      target++;
      return; // simply ignore, we don't do full inlining, it's ok
    }

    // it's really recursive, and we need full inlining.
    // Uh. Buh. Give up.
    err_location(function);
    warning("recursion is ignored");
    target->make_skip();
    
    target++;
    return;
  }

  goto_functionst::function_mapt::iterator m_it=
    goto_functions.function_map.find(identifier);

  if(m_it==goto_functions.function_map.end())
  {
    if(!full)
    {
      target++;
      return; // simply ignore, we don't do full inlining, it's ok
    }

    err_location(function);
    str << "failed to find function `" << identifier
        << "'";
    throw 0;
  }
  
  const goto_functionst::goto_functiont &f=m_it->second;

  // see if we need to inline this  
  if(!full)
  {
    if(!f.body_available ||
       (!f.is_inlined() && f.body.instructions.size() > smallfunc_limit))
    {
      target++;
      return;
    }
  }

  if(f.body_available)
  {
    recursion_sett::iterator recursion_it=
      recursion_set.insert(identifier).first;  

    // first make sure that this one is already inlined
    goto_inline_rec(m_it, full);

    goto_programt tmp2;
    tmp2.copy_from(f.body);
    
    assert(tmp2.instructions.back().is_end_function());
    tmp2.instructions.back().type=LOCATION;
    
    replace_return(tmp2, lhs, constrain);

    goto_programt tmp;
    parameter_assignments(tmp2.instructions.front().location, f.type, arguments, tmp);
    tmp.destructive_append(tmp2);

    if(f.type.get_bool("#hide"))
    {
      const locationt &new_location=function.find_location();
    
      if(new_location.is_not_nil())
      {
        Forall_goto_program_instructions(it, tmp)
        {
          replace_location(it->location, new_location);
          replace_location(it->guard, new_location);
          replace_location(it->code, new_location);
          it->function=new_location.get_function();
        }
      }
    }

    // set up location instruction for function call  
    target->type=LOCATION;
    target->code.clear();
    
    goto_programt::targett next_target(target);
    next_target++;

    dest.instructions.splice(next_target, tmp.instructions);
    target=next_target;

    recursion_set.erase(recursion_it);
  }
  else // no body available
  {
    if(no_body_set.insert(identifier).second)
    {
      err_location(function);
      str << "no body for function `" << identifier
          << "'";
      warning();
    }

    goto_programt tmp;

    // evaluate function arguments -- they might have
    // pointer dereferencing or the like
    forall_expr(it, arguments)
    {
      goto_programt::targett t=tmp.add_instruction();
      t->make_other();
      t->location=target->location;
      t->function=target->location.get_function();
      t->code=codet(ID_expression);
      t->code.copy_to_operands(*it);
    }
    
    // return value
    if(lhs.is_not_nil())
    {
      exprt rhs=exprt(ID_sideeffect, lhs.type());
      rhs.set(ID_statement, ID_nondet);
      rhs.location()=target->location;

      code_assignt code(lhs, rhs);
      code.location()=target->location;
    
      goto_programt::targett t=tmp.add_instruction(ASSIGN);
      t->location=target->location;
      t->function=target->location.get_function();
      t->code.swap(code);
    }

    // now just kill call
    target->type=LOCATION;
    target->code.clear();
    target++;

    // insert tmp
    dest.instructions.splice(target, tmp.instructions);
  }
}

/*******************************************************************\

Function: goto_inlinet::goto_inline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::goto_inline(goto_programt &dest)
{
  goto_inline_rec(dest, true);
  replace_return(dest, 
    static_cast<const exprt &>(get_nil_irep()),
    static_cast<const exprt &>(get_nil_irep()));
}

/*******************************************************************\

Function: goto_inlinet::goto_inline_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::goto_inline_rec(
  goto_functionst::function_mapt::iterator f_it,
  bool full)
{
  // already done?
  
  if(finished_inlining_set.find(f_it->first)!=
     finished_inlining_set.end())
    return; // yes
    
  // do it
  
  goto_inline_rec(f_it->second.body, full);
  
  // remember we did it
 
  finished_inlining_set.insert(f_it->first); 
}

/*******************************************************************\

Function: goto_inlinet::goto_inline_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inlinet::goto_inline_rec(goto_programt &dest, bool full)
{
  bool changed=false;

  for(goto_programt::instructionst::iterator
      it=dest.instructions.begin();
      it!=dest.instructions.end();
      ) // no it++, done by inline_instruction
  {
    if(inline_instruction(dest, full, it))
      changed=true;
  }

  if(changed)
  {
    remove_skip(dest);  
    dest.update();
  }
}

/*******************************************************************\

Function: goto_inlinet::inline_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_inlinet::inline_instruction(
  goto_programt &dest,
  bool full,
  goto_programt::targett &it)
{
  if(it->is_function_call())
  {
    const code_function_callt &call=to_code_function_call(it->code);

    if(call.function().id()==ID_symbol)
    {
      expand_function_call(
        dest, it, call.lhs(), call.function(), call.arguments(),
        static_cast<const exprt &>(get_nil_irep()), full);

      return true;
    }
  }
  else if(it->is_other())
  {
    // these are for Boolean programs
    if(it->code.get(ID_statement)==ID_bp_constrain &&
       it->code.operands().size()==2 &&
       it->code.op0().operands().size()==2 &&
       it->code.op0().op1().get(ID_statement)==ID_function_call)
    {
      expand_function_call(
        dest, it,
        it->code.op0().op0(), // lhs
        it->code.op0().op1().op0(), // function
        it->code.op0().op1().op1().operands(), // arguments
        it->code.op1(), // constraint
        full);

      return true;
    }
  }

  // advance iterator  
  it++;

  return false; 
}

/*******************************************************************\

Function: goto_inline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler)
{
  goto_inlinet goto_inline(goto_functions, ns, message_handler);

  try
  {
    // find main
    goto_functionst::function_mapt::iterator it=
      goto_functions.function_map.find(ID_main);
      
    if(it==goto_functions.function_map.end())
      return;
    
    goto_inline.goto_inline(it->second.body);
  }

  catch(int)
  {
    goto_inline.error();
  }

  catch(const char *e)
  {
    goto_inline.error(e);
  }

  catch(const std::string &e)
  {
    goto_inline.error(e);
  }
  
  if(goto_inline.get_error_found())
    throw 0;

  // clean up
  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(it->first!=ID_main)
    {
      it->second.body_available=false;
      it->second.body.clear();
    }
}

/*******************************************************************\

Function: goto_partial_inline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_partial_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  unsigned _smallfunc_limit)
{
  goto_inlinet goto_inline(
    goto_functions,
    ns,
    message_handler);
  
  goto_inline.smallfunc_limit=_smallfunc_limit;

  try
  {
    for(goto_functionst::function_mapt::iterator
        it=goto_functions.function_map.begin();
        it!=goto_functions.function_map.end();
        it++)
      if(it->second.body_available)
        goto_inline.goto_inline_rec(it, false);
  }

  catch(int)
  {
    goto_inline.error();
  }

  catch(const char *e)
  {
    goto_inline.error(e);
  }

  catch(const std::string &e)
  {
    goto_inline.error(e);
  }

  if(goto_inline.get_error_found())
    throw 0;
}
