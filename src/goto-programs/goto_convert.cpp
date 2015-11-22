/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/rename.h>

#include <ansi-c/c_types.h>

#include "goto_convert.h"
#include "goto_convert_class.h"
#include "destructor.h"

/*******************************************************************\

Function: is_empty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_empty(const goto_programt &goto_program)
{
  forall_goto_program_instructions(it, goto_program)
    if(!it->is_skip() ||
       !it->labels.empty() ||
       !it->code.is_nil())
      return false;

  return true;
}

/*******************************************************************\

Function: goto_convertt::finish_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::finish_gotos()
{
  for(gotost::const_iterator it=targets.gotos.begin();
      it!=targets.gotos.end();
      it++)
  {
    goto_programt::instructiont &i=**it;
    
    if(i.code.get_statement()=="non-deterministic-goto")
    {
      const irept &destinations=i.code.find("destinations");

      i.make_goto();
      
      forall_irep(it, destinations.get_sub())
      {
        labelst::const_iterator l_it=
          targets.labels.find(it->id_string());

        if(l_it==targets.labels.end())
        {
          err_location(i.code);
          str << "goto label `" << it->id_string() << "' not found";
          error_msg();
          throw 0;
        }
          
        i.targets.push_back(l_it->second);
      }
    }
    else if(i.is_start_thread())
    {
      const irep_idt &goto_label=i.code.get(ID_destination);

      labelst::const_iterator l_it=
        targets.labels.find(goto_label);

      if(l_it==targets.labels.end())
      {
        err_location(i.code);
        str << "goto label `" << goto_label << "' not found";
        error_msg();
        throw 0;
      }

      i.targets.push_back(l_it->second);
    }
    else if(i.code.get_statement()==ID_goto)
    {
      const irep_idt &goto_label=i.code.get(ID_destination);

      labelst::const_iterator l_it=targets.labels.find(goto_label);

      if(l_it==targets.labels.end())
      {
        err_location(i.code);
        str << "goto label `" << goto_label << "' not found";
        error_msg();
        throw 0;
      }

      i.targets.clear();
      i.targets.push_back(l_it->second);
    }
    else
    {
      err_location(i.code);
      throw "finish_gotos: unexpected goto";
    }
  }
  
  targets.gotos.clear();
}

/*******************************************************************\

Function: goto_convertt::finish_computed_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::finish_computed_gotos(goto_programt &goto_program)
{
  for(computed_gotost::const_iterator
      g_it=targets.computed_gotos.begin();
      g_it!=targets.computed_gotos.end();
      g_it++)
  {
    goto_programt::instructiont &i=**g_it;
    exprt destination=i.code.op0();
    
    assert(destination.id()==ID_dereference);
    assert(destination.operands().size()==1);
    
    exprt pointer=destination.op0();

    // remember the expression for later checks
    i.type=OTHER;
    i.code=code_expressiont(pointer);
    
    // insert huge case-split
    for(labelst::const_iterator
        l_it=targets.labels.begin();
        l_it!=targets.labels.end();
        l_it++)
    {
      exprt label_expr(ID_label, empty_typet());
      label_expr.set(ID_identifier, l_it->first);

      equal_exprt guard;
      
      guard.lhs()=pointer;
      guard.rhs()=address_of_exprt(label_expr);
    
      goto_programt::targett t=
        goto_program.insert_after(*g_it);

      t->make_goto(l_it->second);
      t->source_location=i.source_location;
      t->guard=guard;
    }
  }
  
  targets.computed_gotos.clear();
}

/*******************************************************************\

Function: goto_convertt::goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::goto_convert(const codet &code, goto_programt &dest)
{
  goto_convert_rec(code, dest);
}

/*******************************************************************\

Function: goto_convertt::goto_convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::goto_convert_rec(
  const codet &code,
  goto_programt &dest)
{
  convert(code, dest);

  finish_gotos();
  finish_computed_gotos(dest);
}

/*******************************************************************\

Function: goto_convertt::copy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::copy(
  const codet &code,
  goto_program_instruction_typet type,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction(type);
  t->code=code;
  t->source_location=code.source_location();
}

/*******************************************************************\

Function: goto_convert::convert_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_label(
  const code_labelt &code,
  goto_programt &dest)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "label statement expected to have one operand";
  }
  
  // grab the label
  const irep_idt &label=code.get_label();
  
  goto_programt tmp;

  // magic thread creation label?
  if(has_prefix(id2string(label), "__CPROVER_ASYNC_"))
  {
    // this is like a START_THREAD
    codet tmp_code(ID_start_thread);
    tmp_code.copy_to_operands(code.op0());
    tmp_code.add_source_location()=code.source_location();
    convert(tmp_code, tmp);
  }
  else
    convert(to_code(code.op0()), tmp);
  
  goto_programt::targett target=tmp.instructions.begin();
  dest.destructive_append(tmp);

  targets.labels.insert(std::pair<irep_idt, goto_programt::targett>
                        (label, target));
  target->labels.push_front(label);
}

/*******************************************************************\

Function: goto_convert::convert_gcc_local_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_gcc_local_label(
  const codet &code,
  goto_programt &dest)
{
  // ignore for now
}

/*******************************************************************\

Function: goto_convert::convert_switch_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_switch_case(
  const code_switch_caset &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "switch-case statement expected to have two operands";
  }
  
  goto_programt tmp;
  convert(code.code(), tmp);
  
  goto_programt::targett target=tmp.instructions.begin();
  dest.destructive_append(tmp);

  // default?

  if(code.is_default())
    targets.set_default(target);
  else
  {
    // cases?

    cases_mapt::iterator cases_entry=targets.cases_map.find(target);
    if(cases_entry==targets.cases_map.end())
    {
      targets.cases.push_back(std::make_pair(target, caset()));
      cases_entry=targets.cases_map.insert(std::make_pair(
            target, --targets.cases.end())).first;
    }

    exprt::operandst &case_op_dest=cases_entry->second->second;
    case_op_dest.push_back(code.case_op());
  }
}

/*******************************************************************\

Function: goto_convert::convert_gcc_switch_case_range

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_gcc_switch_case_range(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=3)
  {
    err_location(code);
    throw "GCC's switch-case-range statement expected to have three operands";
  }
  
  goto_programt tmp;
  convert(to_code(code.op2()), tmp);
  
  //goto_programt::targett target=tmp.instructions.begin();
  dest.destructive_append(tmp);

  #if 0
  cases_mapt::iterator cases_entry=targets.cases_map.find(target);
  if(cases_entry==targets.cases_map.end())
  {
    targets.cases.push_back(std::make_pair(target, caset()));
    cases_entry=targets.cases_map.insert(std::make_pair(
          target, --targets.cases.end())).first;
  }

  // TODO
  exprt::operandst &case_op_dest=cases_entry->second->second;
  case_op_dest.push_back(code.case_op());
  #endif
}

/*******************************************************************\

Function: goto_convertt::convert

  Inputs:

 Outputs:

 Purpose: converts 'code' and appends the result to 'dest'

\*******************************************************************/

void goto_convertt::convert(
  const codet &code,
  goto_programt &dest)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_block)
    convert_block(to_code_block(code), dest);
  else if(statement==ID_decl)
    convert_decl(to_code_decl(code), dest);
  else if(statement==ID_decl_type)
    convert_decl_type(code, dest);
  else if(statement==ID_expression)
    convert_expression(to_code_expression(code), dest);
  else if(statement==ID_assign)
    convert_assign(to_code_assign(code), dest);
  else if(statement==ID_init)
    convert_init(code, dest);
  else if(statement==ID_assert)
    convert_assert(to_code_assert(code), dest);
  else if(statement==ID_assume)
    convert_assume(to_code_assume(code), dest);
  else if(statement==ID_function_call)
    convert_function_call(to_code_function_call(code), dest);
  else if(statement==ID_label)
    convert_label(to_code_label(code), dest);
  else if(statement==ID_gcc_local_label)
    convert_gcc_local_label(code, dest);
  else if(statement==ID_switch_case)
    convert_switch_case(to_code_switch_case(code), dest);
  else if(statement==ID_gcc_switch_case_range)
    convert_gcc_switch_case_range(code, dest);
  else if(statement==ID_for)
    convert_for(to_code_for(code), dest);
  else if(statement==ID_while)
    convert_while(to_code_while(code), dest);
  else if(statement==ID_dowhile)
    convert_dowhile(code, dest);
  else if(statement==ID_switch)
    convert_switch(to_code_switch(code), dest);
  else if(statement==ID_break)
    convert_break(to_code_break(code), dest);
  else if(statement==ID_return)
    convert_return(to_code_return(code), dest);
  else if(statement==ID_continue)
    convert_continue(to_code_continue(code), dest);
  else if(statement==ID_goto)
    convert_goto(code, dest);
  else if(statement==ID_gcc_computed_goto)
    convert_gcc_computed_goto(code, dest);
  else if(statement==ID_skip)
    convert_skip(code, dest);
  else if(statement=="non-deterministic-goto")
    convert_non_deterministic_goto(code, dest);
  else if(statement==ID_ifthenelse)
    convert_ifthenelse(to_code_ifthenelse(code), dest);
  else if(statement==ID_specc_notify)
    convert_specc_notify(code, dest);
  else if(statement==ID_specc_wait)
    convert_specc_wait(code, dest);
  else if(statement==ID_specc_par)
    convert_specc_par(code, dest);
  else if(statement==ID_start_thread)
    convert_start_thread(code, dest);
  else if(statement==ID_end_thread)
    convert_end_thread(code, dest);
  else if(statement==ID_atomic_begin)
    convert_atomic_begin(code, dest);
  else if(statement==ID_atomic_end)
    convert_atomic_end(code, dest);
  else if(statement==ID_bp_enforce)
    convert_bp_enforce(code, dest);
  else if(statement==ID_bp_abortif)
    convert_bp_abortif(code, dest);
  else if(statement==ID_cpp_delete ||
          statement=="cpp_delete[]")
    convert_cpp_delete(code, dest);
  else if(statement==ID_msc_try_except)
    convert_msc_try_except(code, dest);
  else if(statement==ID_msc_try_finally)
    convert_msc_try_finally(code, dest);
  else if(statement==ID_msc_leave)
    convert_msc_leave(code, dest);
  else if(statement==ID_try_catch) // C++ try/catch
    convert_try_catch(code, dest);
  else if(statement==ID_CPROVER_try_catch) // CPROVER-homemade
    convert_CPROVER_try_catch(code, dest);
  else if(statement==ID_CPROVER_throw) // CPROVER-homemade
    convert_CPROVER_throw(code, dest);
  else if(statement==ID_CPROVER_try_finally)
    convert_CPROVER_try_finally(code, dest);
  else if(statement==ID_asm)
    convert_asm(to_code_asm(code), dest);
  else if(statement==ID_static_assert)
  {
    assert(code.operands().size()==2);
    exprt assertion=code.op0();
    assertion.make_typecast(bool_typet());
    simplify(assertion, ns);
    if(assertion.is_false())
    {
      err_location(code.op0());
      str << "static assertion "
          << get_string_constant(code.op1());
      error_msg();
      throw 0;
    }
    else if(assertion.is_true())
    {
    }
    else
    {
      // we may wish to complain
    }
  }
  else if(statement==ID_dead)
    copy(code, DEAD, dest);
  else if(statement==ID_decl_block)
  {
    forall_operands(it, code)
      convert(to_code(*it), dest);
  }
  else
    copy(code, OTHER, dest);

  // make sure dest is never empty
  if(dest.instructions.empty())
  {
    dest.add_instruction(SKIP);
    dest.instructions.back().code.make_nil();
    dest.instructions.back().source_location=code.source_location();
  }
}

/*******************************************************************\

Function: goto_convertt::convert_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_block(
  const code_blockt &code,
  goto_programt &dest)
{
  const source_locationt &end_location=code.end_location();

  // this saves the size of the destructor stack
  std::size_t old_stack_size=targets.destructor_stack.size();
  
  // now convert block  
  forall_operands(it, code)
  {
    const codet &b_code=to_code(*it);
    convert(b_code, dest);
  }

  // see if we need to do any destructors
  unwind_destructor_stack(end_location, old_stack_size, dest);

  // remove those destructors
  targets.destructor_stack.resize(old_stack_size);
}

/*******************************************************************\

Function: goto_convertt::convert_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_expression(
  const code_expressiont &code,
  goto_programt &dest)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "expression statement takes one operand";
  }
  
  exprt expr=code.op0();
  
  if(expr.id()==ID_if)
  {
    // We do a special treatment for c?t:f
    // by compiling to if(c) t; else f;
    const if_exprt &if_expr=to_if_expr(expr);
    code_ifthenelset tmp_code;
    tmp_code.add_source_location()=expr.source_location();
    tmp_code.cond()=if_expr.cond();
    tmp_code.then_case()=code_expressiont(if_expr.true_case());
    tmp_code.then_case().add_source_location()=expr.source_location();
    tmp_code.else_case()=code_expressiont(if_expr.false_case());
    tmp_code.else_case().add_source_location()=expr.source_location();
    convert_ifthenelse(tmp_code, dest);
  }
  else
  {
    clean_expr(expr, dest, false); // result _not_ used

    // Any residual expression? 
    // We keep it to add checks later.
    if(expr.is_not_nil())
    {
      codet tmp=code;
      tmp.op0()=expr;
      tmp.add_source_location()=expr.source_location();
      copy(tmp, OTHER, dest);
    }
  }
}

/*******************************************************************\

Function: goto_convertt::convert_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_decl(
  const code_declt &code,
  goto_programt &dest)
{
  const exprt &op0=code.op0();
    
  if(op0.id()!=ID_symbol)
  {
    err_location(op0);
    throw "decl statement expects symbol as first operand";
  }

  const irep_idt &identifier=op0.get(ID_identifier);
  
  const symbolt &symbol=lookup(identifier);
  
  if(symbol.is_static_lifetime ||
     symbol.type.id()==ID_code)
    return; // this is a SKIP!

  if(code.operands().size()==1)
  {
    copy(code, DECL, dest);
  }
  else
  {
    // this is expected to go away
    exprt initializer;
  
    codet tmp=code;
    initializer=code.op1();
    tmp.operands().resize(1);
    
    // Break up into decl and assignment.
    // Decl must be visible before initializer.
    copy(tmp, DECL, dest);

    code_assignt assign(code.op0(), initializer);
    assign.add_source_location()=tmp.source_location();

    convert_assign(assign, dest);
  }

  // now create a 'dead' instruction -- will be added after the
  // destructor created below as unwind_destructor_stack pops off the
  // top of the destructor stack
  const symbol_exprt symbol_expr(symbol.name, symbol.type);

  {
    code_deadt code_dead(symbol_expr);
    targets.destructor_stack.push_back(code_dead);
  }

  // do destructor
  code_function_callt destructor=get_destructor(ns, symbol.type);

  if(destructor.is_not_nil())
  {
    // add "this"
    exprt this_expr(ID_address_of, pointer_typet());
    this_expr.type().subtype()=symbol.type;
    this_expr.copy_to_operands(symbol_expr);
    destructor.arguments().push_back(this_expr);

    targets.destructor_stack.push_back(destructor);
  }
}

/*******************************************************************\

Function: goto_convertt::convert_decl_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_decl_type(
  const codet &code,
  goto_programt &dest)
{
  // we remove these
}

/*******************************************************************\

Function: goto_convertt::convert_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_assign(
  const code_assignt &code,
  goto_programt &dest)
{
  exprt lhs=code.lhs(),
        rhs=code.rhs();

  clean_expr(lhs, dest);

  if(rhs.id()==ID_side_effect &&
     rhs.get(ID_statement)==ID_function_call)
  {
    if(rhs.operands().size()!=2)
    {
      err_location(rhs);
      throw "function_call sideeffect takes two operands";
    }
  
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    do_function_call(lhs, rhs.op0(), rhs.op1().operands(), dest);
  }
  else if(rhs.id()==ID_side_effect &&
          (rhs.get(ID_statement)==ID_cpp_new ||
           rhs.get(ID_statement)==ID_cpp_new_array))
  {
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    do_cpp_new(lhs, to_side_effect_expr(rhs), dest);
  }
  else if(rhs.id()==ID_side_effect &&
          rhs.get(ID_statement)==ID_java_new)
  {
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    do_java_new(lhs, to_side_effect_expr(rhs), dest);
  }
  else if(rhs.id()==ID_side_effect &&
          rhs.get(ID_statement)==ID_java_new_array)
  {
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    do_java_new_array(lhs, to_side_effect_expr(rhs), dest);
  }
  else if(rhs.id()==ID_side_effect &&
          rhs.get(ID_statement)==ID_malloc)
  {
    // just preserve
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    code_assignt new_assign(code);
    new_assign.lhs()=lhs;
    new_assign.rhs()=rhs;

    copy(new_assign, ASSIGN, dest);
  }
  else
  {
    clean_expr(rhs, dest);
    
    if(lhs.id()==ID_typecast)
    {
      assert(lhs.operands().size()==1);

      // add a typecast to the rhs
      exprt new_rhs=rhs;
      rhs.make_typecast(lhs.op0().type());

      // remove typecast from lhs      
      exprt tmp=lhs.op0();
      lhs.swap(tmp);      
    }

    code_assignt new_assign(code);
    new_assign.lhs()=lhs;
    new_assign.rhs()=rhs;

    copy(new_assign, ASSIGN, dest);
  }
}

/*******************************************************************\

Function: goto_convertt::convert_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_init(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "init statement takes two operands";
  }
  
  // make it an assignment
  codet assignment=code;
  assignment.set_statement(ID_assign);

  convert(to_code_assign(assignment), dest);
}

/*******************************************************************\

Function: goto_convertt::convert_cpp_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_cpp_delete(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "cpp_delete statement takes one operand";
  }
  
  exprt tmp_op=code.op0();
  
  clean_expr(tmp_op, dest);
  
  // we call the destructor, and then free
  const exprt &destructor=
    static_cast<const exprt &>(code.find(ID_destructor));
    
  irep_idt delete_identifier;
  
  if(code.get_statement()==ID_cpp_delete_array)
    delete_identifier="__delete_array";
  else if(code.get_statement()==ID_cpp_delete)
    delete_identifier="__delete";
  else
    assert(false);
  
  if(destructor.is_not_nil())
  {
    if(code.get_statement()==ID_cpp_delete_array)
    {
      // build loop

    }
    else if(code.get_statement()==ID_cpp_delete)
    {
      // just one object
      exprt deref_op(ID_dereference, tmp_op.type().subtype());
      deref_op.copy_to_operands(tmp_op);
      
      codet tmp_code=to_code(destructor);
      replace_new_object(deref_op, tmp_code);
      convert(tmp_code, dest);
    }
    else
      assert(false);
  }
  
  // now do "free"
  exprt delete_symbol=ns.lookup(delete_identifier).symbol_expr();
  
  assert(to_code_type(delete_symbol.type()).parameters().size()==1);

  typet arg_type=
    to_code_type(delete_symbol.type()).parameters().front().type();
  
  code_function_callt delete_call;
  delete_call.function()=delete_symbol;
  delete_call.arguments().push_back(typecast_exprt(tmp_op, arg_type));
  delete_call.lhs().make_nil();
  delete_call.add_source_location()=code.source_location();
  
  convert(delete_call, dest);  
}

/*******************************************************************\

Function: goto_convertt::convert_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_assert(
  const code_assertt &code,
  goto_programt &dest)
{
  exprt cond=code.assertion();

  clean_expr(cond, dest);
  
  goto_programt::targett t=dest.add_instruction(ASSERT);
  t->guard.swap(cond);
  t->source_location=code.source_location();
  t->source_location.set(ID_property, ID_assertion);
  t->source_location.set("user-provided", true);
}

/*******************************************************************\

Function: goto_convertt::convert_skip

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_skip(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction(SKIP);
  t->source_location=code.source_location();
  t->code=code;
}

/*******************************************************************\

Function: goto_convertt::convert_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_assume(
  const code_assumet &code,
  goto_programt &dest)
{
  exprt op=code.assumption();

  clean_expr(op, dest);

  goto_programt::targett t=dest.add_instruction(ASSUME);
  t->guard.swap(op);
  t->source_location=code.source_location();
}

/*******************************************************************\

Function: goto_convertt::convert_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_for(
  const code_fort &code,
  goto_programt &dest)
{
  // turn for(A; c; B) { P } into
  //  A; while(c) { P; B; }
  //-----------------------------
  //    A;
  // u: sideeffects in c 
  // v: if(!c) goto z;
  // w: P;
  // x: B;               <-- continue target
  // y: goto u;
  // z: ;                <-- break target

  // A;
  if(code.init().is_not_nil())
    convert(to_code(code.init()), dest);
    
  exprt cond=code.cond();

  goto_programt sideeffects;
  clean_expr(cond, sideeffects);

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the u label
  goto_programt::targett u=sideeffects.instructions.begin();

  // do the v label
  goto_programt tmp_v;
  goto_programt::targett v=tmp_v.add_instruction();
  
  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction(SKIP);
  z->source_location=code.source_location();

  // do the x label
  goto_programt tmp_x;
  
  if(code.op2().is_nil())
  {
    tmp_x.add_instruction(SKIP);
    tmp_x.instructions.back().source_location=code.source_location();
  }
  else
  {
    exprt tmp_B=code.iter();

    clean_expr(tmp_B, tmp_x, false);

    if(tmp_x.instructions.empty())
    {
      tmp_x.add_instruction(SKIP);
      tmp_x.instructions.back().source_location=code.source_location();
    }
  }
  
  // optimize the v label
  if(sideeffects.instructions.empty())
    u=v;

  // set the targets
  targets.set_break(z);
  targets.set_continue(tmp_x.instructions.begin());

  // v: if(!c) goto z;
  v->make_goto(z);
  v->guard=cond;
  v->guard.make_not();
  v->source_location=cond.source_location();

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w);
  
  // y: goto u;
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();
  y->make_goto(u);
  y->guard=true_exprt();
  y->source_location=code.source_location();

  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  old_targets.restore(targets);
}

/*******************************************************************\

Function: goto_convertt::convert_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_while(
  const code_whilet &code,
  goto_programt &dest)
{
  const exprt &cond=code.cond();
  const source_locationt &source_location=code.source_location();

  //    while(c) P;
  //--------------------
  // v: sideeffects in c
  //    if(!c) goto z;
  // x: P;
  // y: goto v;          <-- continue target
  // z: ;                <-- break target

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=source_location;

  goto_programt tmp_branch;
  generate_conditional_branch(boolean_negate(cond), z, source_location, tmp_branch);

  // do the v label
  goto_programt::targett v=tmp_branch.instructions.begin();

  // do the y label
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();

  // set the targets
  targets.set_break(z);
  targets.set_continue(y);

  // do the x label
  goto_programt tmp_x;
  convert(code.body(), tmp_x);

  // y: if(c) goto v;
  y->make_goto(v);
  y->guard=true_exprt();
  y->source_location=code.source_location();

  dest.destructive_append(tmp_branch);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  old_targets.restore(targets);
}

/*******************************************************************\

Function: goto_convertt::convert_dowhile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_dowhile(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "dowhile takes two operands";
  }

  // save source location  
  source_locationt condition_location=code.op0().find_source_location();

  exprt cond=code.op0();

  goto_programt sideeffects;
  clean_expr(cond, sideeffects);  

  //    do P while(c);
  //--------------------
  // w: P;
  // x: sideeffects in c   <-- continue target
  // y: if(c) goto w;
  // z: ;                  <-- break target

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the y label
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=code.source_location();

  // do the x label
  goto_programt::targett x;
  if(sideeffects.instructions.empty())
    x=y;
  else
    x=sideeffects.instructions.begin();

  // set the targets
  targets.set_break(z);
  targets.set_continue(x);

  // do the w label
  goto_programt tmp_w;
  convert(to_code(code.op1()), tmp_w);
  goto_programt::targett w=tmp_w.instructions.begin();

  // y: if(c) goto w;
  y->make_goto(w);
  y->guard=cond;
  y->source_location=condition_location;

  dest.destructive_append(tmp_w);
  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue targets
  old_targets.restore(targets);
}

/*******************************************************************\

Function: goto_convertt::case_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_convertt::case_guard(
  const exprt &value,
  const exprt::operandst &case_op)
{
  exprt dest=exprt(ID_or, bool_typet());
  dest.reserve_operands(case_op.size());

  forall_expr(it, case_op)
  {
    equal_exprt eq_expr;
    eq_expr.lhs()=value;
    eq_expr.rhs()=*it;
    dest.move_to_operands(eq_expr);
  }

  assert(!dest.operands().empty());

  if(dest.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(dest.op0());
    dest.swap(tmp);
  }
  
  return dest;
}

/*******************************************************************\

Function: goto_convertt::convert_switch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_switch(
  const code_switcht &code,
  goto_programt &dest)
{
  // switch(v) {
  //   case x: Px;
  //   case y: Py;
  //   ...
  //   default: Pd;
  // }
  // --------------------
  // x: if(v==x) goto X;
  // y: if(v==y) goto Y;
  //    goto d;
  // X: Px;
  // Y: Py;
  // d: Pd;
  // z: ;

  if(code.operands().size()<2)
  {
    err_location(code);
    throw "switch takes at least two operands";
  }
  
  exprt argument=code.value();

  goto_programt sideeffects;
  clean_expr(argument, sideeffects);

  // save break/default/cases targets
  break_switch_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=code.source_location();

  // set the new targets -- continue stays as is
  targets.set_break(z);
  targets.set_default(z);
  targets.cases.clear();
  targets.cases_map.clear();

  goto_programt tmp;

  forall_operands(it, code)
    if(it!=code.operands().begin())
      convert(to_code(*it), tmp);

  goto_programt tmp_cases;

  for(casest::iterator it=targets.cases.begin();
      it!=targets.cases.end();
      it++)
  {
    const caset &case_ops=it->second;
  
    assert(!case_ops.empty());    
  
    exprt guard_expr=case_guard(argument, case_ops);

    goto_programt::targett x=tmp_cases.add_instruction();
    x->make_goto(it->first);
    x->guard.swap(guard_expr);
    x->source_location=case_ops.front().find_source_location();
  }

  {
    goto_programt::targett d_jump=tmp_cases.add_instruction();
    d_jump->make_goto(targets.default_target);
    d_jump->source_location=targets.default_target->source_location;
  }

  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_cases);
  dest.destructive_append(tmp);
  dest.destructive_append(tmp_z);

  // restore old targets
  old_targets.restore(targets);
}

/*******************************************************************\

Function: goto_convertt::convert_break

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_break(
  const code_breakt &code,
  goto_programt &dest)
{
  if(!targets.break_set)
  {
    err_location(code);
    throw "break without target";
  }

  // need to process destructor stack
  unwind_destructor_stack(code.source_location(), targets.break_stack_size, dest);

  // add goto
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.break_target);
  t->source_location=code.source_location();
}

/*******************************************************************\

Function: goto_convertt::convert_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_return(
  const code_returnt &code,
  goto_programt &dest)
{
  if(!targets.return_set)
  {
    err_location(code);
    throw "return without target";
  }

  if(!code.operands().empty() &&
     code.operands().size()!=1)
  {
    err_location(code);
    throw "return takes none or one operand";
  }
  
  code_returnt new_code(code);
  
  if(new_code.has_return_value())
  {
    bool result_is_used=
      new_code.return_value().type().id()!=ID_empty;
  
    goto_programt sideeffects;
    clean_expr(new_code.return_value(), sideeffects, result_is_used);
    dest.destructive_append(sideeffects);

    // remove void-typed return value
    if(!result_is_used)
      new_code.operands().resize(0);    
  }

  if(targets.has_return_value)
  {
    if(!new_code.has_return_value())
    {
      err_location(new_code);
      throw "function must return value";
    }

    // Now add a return node to set the return value.
    goto_programt::targett t=dest.add_instruction();
    t->make_return();
    t->code=new_code;
    t->source_location=new_code.source_location();
  }
  else
  {
    if(new_code.has_return_value() &&
       new_code.return_value().type().id()!=ID_empty)
    {
      err_location(new_code);
      throw "function must not return value";
    }
  }
  
  // Need to process _entire_ destructor stack.
  unwind_destructor_stack(code.source_location(), 0, dest);
  
  // add goto to end-of-function
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.return_target, true_exprt());
  t->source_location=new_code.source_location();
}

/*******************************************************************\

Function: goto_convertt::convert_continue

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_continue(
  const code_continuet &code,
  goto_programt &dest)
{
  if(!targets.continue_set)
  {
    err_location(code);
    throw "continue without target";
  }

  // need to process destructor stack
  unwind_destructor_stack(code.source_location(), targets.continue_stack_size, dest);

  // add goto
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.continue_target);
  t->source_location=code.source_location();
}

/*******************************************************************\

Function: goto_convertt::convert_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_goto(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction();
  t->make_goto();
  t->source_location=code.source_location();
  t->code=code;

  // remember it to do target later
  targets.gotos.push_back(t);
}

/*******************************************************************\

Function: goto_convertt::convert_gcc_computed_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_gcc_computed_goto(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction();
  t->make_skip();
  t->source_location=code.source_location();
  t->code=code;

  // remember it to do this later
  targets.computed_gotos.push_back(t);
}

/*******************************************************************\

Function: goto_convertt::convert_non_deterministic_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_non_deterministic_goto(
  const codet &code,
  goto_programt &dest)
{
  convert_goto(code, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_specc_notify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_specc_notify(
  const codet &code,
  goto_programt &dest)
{
  #if 0
  goto_programt::targett t=dest.add_instruction(EVENT);

  forall_operands(it, code)
    convert_specc_event(*it, t->events);

  t->code.swap(code);
  t->source_location=code.source_location();
  #endif

  copy(code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_specc_event

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_specc_event(
  const exprt &op,
  std::set<irep_idt> &events)
{
  if(op.id()==ID_or || op.id()==ID_and)
  {
    forall_operands(it, op)
      convert_specc_event(*it, events);
  }
  else if(op.id()==ID_specc_event)
  {
    irep_idt event=op.get(ID_identifier);

    if(has_prefix(id2string(event), "specc::"))
      event=std::string(id2string(event), 7, std::string::npos);

    events.insert(event);
  }
  else
  {
    err_location(op);
    throw "convert_convert_event got "+op.id_string();
  }
}

/*******************************************************************\

Function: goto_convertt::convert_specc_wait

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_specc_wait(
  const codet &code,
  goto_programt &dest)
{
  #if 0
  goto_programt::targett t=dest.add_instruction(WAIT);
  
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "specc_wait expects one operand";
  }

  const exprt &op=code.op0();

  if(op.id()=="or")
    t->or_semantics=true;

  convert_specc_event(op, t->events);

  t->code.swap(code);
  t->source_location=code.source_location();
  #endif

  copy(code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_specc_par

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_specc_par(
  const codet &code,
  goto_programt &dest)
{
  copy(code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_start_thread(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "start_thread expects one operand";
  }

  goto_programt::targett start_thread=
    dest.add_instruction(START_THREAD);

  start_thread->source_location=code.source_location();
  
  {
    // start_thread label;
    // goto tmp;
    // label: op0-code
    // end_thread
    // tmp: skip
    
    goto_programt::targett goto_instruction=dest.add_instruction(GOTO);
    goto_instruction->guard=true_exprt();
    goto_instruction->source_location=code.source_location();

    goto_programt tmp;
    convert(to_code(code.op0()), tmp);
    goto_programt::targett end_thread=tmp.add_instruction(END_THREAD);
    end_thread->source_location=code.source_location();
    
    start_thread->targets.push_back(tmp.instructions.begin());
    dest.destructive_append(tmp);
    goto_instruction->targets.push_back(dest.add_instruction(SKIP));
    dest.instructions.back().source_location=code.source_location();
  }
}

/*******************************************************************\

Function: goto_convertt::convert_end_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_end_thread(
  const codet &code,
  goto_programt &dest)
{
  if(!code.operands().empty())
  {
    err_location(code);
    throw "end_thread expects no operands";
  }

  copy(code, END_THREAD, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_atomic_begin(
  const codet &code,
  goto_programt &dest)
{
  if(!code.operands().empty())
  {
    err_location(code);
    throw "atomic_begin expects no operands";
  }

  copy(code, ATOMIC_BEGIN, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_atomic_end(
  const codet &code,
  goto_programt &dest)
{
  if(!code.operands().empty())
  {
    err_location(code);
    throw "atomic_end expects no operands";
  }

  copy(code, ATOMIC_END, dest);
}

/*******************************************************************\

Function: goto_convertt::convert_bp_enforce

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_bp_enforce(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    str << "bp_enfroce expects two arguments";
    error_msg();
    throw 0;
  }
    
  // do an assume
  exprt op=code.op0();

  clean_expr(op, dest);

  goto_programt::targett t=dest.add_instruction(ASSUME);
  t->guard=op;
  t->source_location=code.source_location();

  // change the assignments
  
  goto_programt tmp;
  convert(to_code(code.op1()), tmp);
  
  if(!op.is_true())
  {
    exprt constraint(op);
    make_next_state(constraint);
  
    Forall_goto_program_instructions(it, tmp)
    {
      if(it->is_assign())
      {
        assert(it->code.get(ID_statement)==ID_assign);

        // add constrain
        codet constrain(ID_bp_constrain);
        constrain.reserve_operands(2);
        constrain.move_to_operands(it->code);
        constrain.copy_to_operands(constraint);
        it->code.swap(constrain);

        it->type=OTHER;
      }
      else if(it->is_other() &&
              it->code.get(ID_statement)==ID_bp_constrain)
      {
        // add to constraint
        assert(it->code.operands().size()==2);
        it->code.op1()=
          and_exprt(it->code.op1(), constraint);
      }
    }
  }
  
  dest.destructive_append(tmp);
}

/*******************************************************************\

Function: goto_convertt::convert_bp_abortif

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_bp_abortif(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "bp_abortif expects one argument";
  }
    
  // do an assert
  exprt op=code.op0();

  clean_expr(op, dest);
  
  op.make_not();

  goto_programt::targett t=dest.add_instruction(ASSERT);
  t->guard.swap(op);
  t->source_location=code.source_location();
}

/*******************************************************************\

Function: goto_convertt::convert_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_ifthenelse(
  const code_ifthenelset &code,
  goto_programt &dest)
{
  if(code.operands().size()!=3)
  {
    err_location(code);
    throw "ifthenelse takes three operands";
  }
  
  assert(code.then_case().is_not_nil());
  
  bool has_else=
    !code.else_case().is_nil();

  const source_locationt &source_location=code.source_location();

  // We do a bit of special treatment for && in the condition
  // in case cleaning would be needed otherwise.
  if(code.cond().id()==ID_and &&
     code.cond().operands().size()==2 &&
     (needs_cleaning(code.cond().op0()) || needs_cleaning(code.cond().op1())) &&
     !has_else)
  {
    // if(a && b) XX --> if(a) if(b) XX
    code_ifthenelset new_if0, new_if1;
    new_if0.cond()=code.cond().op0();
    new_if1.cond()=code.cond().op1();
    new_if0.add_source_location()=source_location;
    new_if1.add_source_location()=source_location;
    new_if1.then_case()=code.then_case();
    new_if0.then_case()=new_if1;
    return convert_ifthenelse(new_if0, dest);
  }

  // convert 'then'-branch
  goto_programt tmp_then;
  convert(to_code(code.then_case()), tmp_then);

  goto_programt tmp_else;

  if(has_else)
    convert(to_code(code.else_case()), tmp_else);

  exprt tmp_guard=code.cond();
  clean_expr(tmp_guard, dest);

  generate_ifthenelse(tmp_guard, tmp_then, tmp_else, source_location, dest);
}

/*******************************************************************\

Function: goto_convertt::collect_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::collect_operands(
  const exprt &expr,
  const irep_idt &id,
  std::list<exprt> &dest)
{
  if(expr.id()!=id)
  {
    dest.push_back(expr);
  }
  else
  {
    // left-to-right is important
    forall_operands(it, expr)
      collect_operands(*it, id, dest);
  }
}

/*******************************************************************\

Function: goto_convertt::generate_ifthenelse

  Inputs:

 Outputs:

 Purpose: if(guard) true_case; else false_case;

\*******************************************************************/

void goto_convertt::generate_ifthenelse(
  const exprt &guard,
  goto_programt &true_case,
  goto_programt &false_case,
  const source_locationt &source_location,
  goto_programt &dest)
{
  if(is_empty(true_case) &&
     is_empty(false_case))
    return;

  // do guarded gotos directly
  if(is_empty(false_case) &&
     // true_case.instructions.size()==1 optimised
     !true_case.instructions.empty() &&
     ++true_case.instructions.begin()==true_case.instructions.end() &&
     true_case.instructions.back().is_goto() &&
     true_case.instructions.back().guard.is_true() &&
     true_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) { label: goto somewhere; }
    true_case.instructions.back().guard=guard;
    dest.destructive_append(true_case);
    return;
  }
  
  // similarly, do guarded assertions directly
  if(true_case.instructions.size()==1 &&
     true_case.instructions.back().is_assert() &&
     true_case.instructions.back().guard.is_false() &&
     true_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) { label: assert(0); }
    true_case.instructions.back().guard=boolean_negate(guard);
    dest.destructive_append(true_case);
    true_case.instructions.clear();
  }

  // similarly, do guarded assertions directly
  if(false_case.instructions.size()==1 &&
     false_case.instructions.back().is_assert() &&
     false_case.instructions.back().guard.is_false() &&
     false_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) ... else { label: assert(0); }
    false_case.instructions.back().guard=guard;
    dest.destructive_append(false_case);
    false_case.instructions.clear();
  }

  // Flip around if no 'true' case code.
  if(is_empty(true_case))
    return generate_ifthenelse(
      boolean_negate(guard), false_case, true_case, source_location, dest);

  bool has_else=!is_empty(false_case);

  //    if(c) P;
  //--------------------
  // v: if(!c) goto z;
  // w: P;
  // z: ;

  //    if(c) P; else Q;
  //--------------------
  // v: if(!c) goto y;
  // w: P;
  // x: goto z;
  // y: Q;
  // z: ;

  // do the x label
  goto_programt tmp_x;
  goto_programt::targett x=tmp_x.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=source_location;

  // y: Q;
  goto_programt tmp_y;
  goto_programt::targett y;
  if(has_else)
  {
    tmp_y.swap(false_case);
    y=tmp_y.instructions.begin();
  }

  // v: if(!c) goto z/y;
  goto_programt tmp_v;
  generate_conditional_branch(
    boolean_negate(guard), has_else?y:z, source_location, tmp_v);

  // w: P;
  goto_programt tmp_w;
  tmp_w.swap(true_case);

  // x: goto z;
  x->make_goto(z);
  assert(!tmp_w.instructions.empty());
  x->source_location=tmp_w.instructions.back().source_location;

  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);

  if(has_else)
  {
    dest.destructive_append(tmp_x);
    dest.destructive_append(tmp_y);
  }

  dest.destructive_append(tmp_z);
}

/*******************************************************************\

Function: goto_convertt::generate_conditional_branch

  Inputs:

 Outputs:

 Purpose: if(guard) goto target;

\*******************************************************************/

static bool has_and_or(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_and_or(*it)) return true;

  if(expr.id()==ID_and || expr.id()==ID_or)
    return true;
    
  return false;
}

void goto_convertt::generate_conditional_branch(
  const exprt &guard,
  goto_programt::targett target_true,
  const source_locationt &source_location,
  goto_programt &dest)
{
  if(has_and_or(guard) && needs_cleaning(guard))
  {
    // if(guard) goto target;
    //   becomes
    // if(guard) goto target; else goto next;
    // next: skip;

    goto_programt tmp;
    goto_programt::targett target_false=tmp.add_instruction();
    target_false->make_skip();
    target_false->source_location=source_location;
    
    generate_conditional_branch(
      guard, target_true, target_false, source_location, dest);
    
    dest.destructive_append(tmp);
  }
  else
  {
    // simple branch
    exprt cond=guard;
    clean_expr(cond, dest);
  
    goto_programt tmp;
    goto_programt::targett g=tmp.add_instruction();
    g->make_goto(target_true);
    g->guard=cond;
    g->source_location=source_location;
    dest.destructive_append(tmp);
  }
}

/*******************************************************************\

Function: goto_convertt::generate_conditional_branch

  Inputs:

 Outputs:

 Purpose: if(guard) goto target_true; else goto target_false;

\*******************************************************************/

void goto_convertt::generate_conditional_branch(
  const exprt &guard,
  goto_programt::targett target_true,
  goto_programt::targett target_false,
  const source_locationt &source_location,
  goto_programt &dest)
{
  if(guard.id()==ID_not)
  {
    assert(guard.operands().size()==1);
    // simply swap targets
    generate_conditional_branch(
      guard.op0(), target_false, target_true, source_location, dest);
    return;
  }

  if(guard.id()==ID_and)
  {
    // turn
    //   if(a && b) goto target_true; else goto target_false;
    // into
    //    if(!a) goto target_false;
    //    if(!b) goto target_false;
    //    goto target_true;
    
    std::list<exprt> op;
    collect_operands(guard, guard.id(), op);
  
    forall_expr_list(it, op)
      generate_conditional_branch(
        boolean_negate(*it), target_false, source_location, dest);

    goto_programt::targett t_true=dest.add_instruction();
    t_true->make_goto(target_true);
    t_true->guard=true_exprt();
    t_true->source_location=source_location;
    
    return;
  }
  else if(guard.id()==ID_or)
  {
    // turn
    //   if(a || b) goto target_true; else goto target_false;
    // into
    //   if(a) goto target_true;
    //   if(b) goto target_true;
    //   goto target_false;

    std::list<exprt> op;
    collect_operands(guard, guard.id(), op);
  
    forall_expr_list(it, op)
      generate_conditional_branch(
        *it, target_true, source_location, dest);

    goto_programt::targett t_false=dest.add_instruction();
    t_false->make_goto(target_false);
    t_false->guard=true_exprt();
    t_false->source_location=guard.source_location();
    
    return;
  }

  exprt cond=guard;
  clean_expr(cond, dest);
  
  goto_programt::targett t_true=dest.add_instruction();
  t_true->make_goto(target_true);
  t_true->guard=cond;
  t_true->source_location=source_location;

  goto_programt::targett t_false=dest.add_instruction();
  t_false->make_goto(target_false);
  t_false->guard=true_exprt();
  t_false->source_location=source_location;
}

/*******************************************************************\

Function: goto_convertt::get_string_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt goto_convertt::get_string_constant(
  const exprt &expr)
{
  if(expr.id()==ID_typecast &&
     expr.operands().size()==1)
    return get_string_constant(expr.op0());

  if(expr.id()==ID_address_of &&
     expr.operands().size()==1 &&
     expr.op0().id()==ID_index &&
     expr.op0().operands().size()==2)
  {
    exprt index_op=get_constant(expr.op0().op0());
    simplify(index_op, ns);
    
    if(index_op.id()==ID_string_constant)
      return index_op.get(ID_value);
    else if(index_op.id()==ID_array)
    {
      std::string result;
      forall_operands(it, index_op)
        if(it->is_constant())
        {
          unsigned i=integer2long(
            binary2integer(id2string(to_constant_expr(*it).get_value()), true));

          if(i!=0) // to skip terminating 0
            result+=char(i);
        }
          
      return result;
    }
  }

  if(expr.id()==ID_string_constant)
    return expr.get(ID_value);

  err_location(expr);
  str << "expected string constant, but got: "
      << expr.pretty();
  error_msg();

  throw 0;
}

/*******************************************************************\

Function: goto_convertt::get_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_convertt::get_constant(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_expr(expr));

    return symbol.value;
  }
  else if(expr.id()==ID_member)
  {
    exprt tmp=expr;
    tmp.op0()=get_constant(expr.op0());
    return tmp;
  }
  else if(expr.id()==ID_index)
  {
    exprt tmp=expr;
    tmp.op0()=get_constant(expr.op0());
    tmp.op1()=get_constant(expr.op1());
    return tmp;
  }
  else
    return expr;
}

/*******************************************************************\

Function: goto_convertt::new_tmp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &goto_convertt::new_tmp_symbol(
  const typet &type,
  const std::string &suffix,
  goto_programt &dest,
  const source_locationt &source_location)
{
  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;
  
  do
  {
    new_symbol.base_name="tmp_"+suffix+"$"+i2string(++temporary_counter);
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);
    new_symbol.type=type;    
    new_symbol.location=source_location;
  } while(symbol_table.move(new_symbol, symbol_ptr));    
  
  tmp_symbols.push_back(symbol_ptr->name);
  
  goto_programt::targett t=dest.add_instruction(DECL);
  t->code=code_declt(symbol_ptr->symbol_expr());
  t->source_location=source_location;

  return *symbol_ptr;  
}

/*******************************************************************\

Function: goto_convertt::make_temp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::make_temp_symbol(
  exprt &expr,
  const std::string &suffix,
  goto_programt &dest)
{
  const source_locationt source_location=expr.find_source_location();
  
  symbolt &new_symbol=
    new_tmp_symbol(expr.type(), suffix, dest, source_location);

  code_assignt assignment;
  assignment.lhs()=new_symbol.symbol_expr();
  assignment.rhs()=expr;
  assignment.add_source_location()=source_location;

  convert(assignment, dest);

  expr=new_symbol.symbol_expr();
}

/*******************************************************************\

Function: goto_convertt::new_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::new_name(symbolt &symbol)
{
  // rename it
  get_new_name(symbol, ns);

  // store in symbol_table
  symbol_table.add(symbol);
}

/*******************************************************************\

Function: goto_convertt::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &goto_convertt::lookup(const irep_idt &identifier) const
{
  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
    throw "failed to find symbol "+id2string(identifier);
  return *symbol;
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  const codet &code,
  symbol_tablet &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler)
{
  goto_convertt goto_convert(symbol_table, message_handler);

  try
  {
    goto_convert.goto_convert(code, dest);
  }
  
  catch(int)
  {
    goto_convert.error_msg();
  }

  catch(const char *e)
  {
    goto_convert.str << e;
    goto_convert.error_msg();
  }

  catch(const std::string &e)
  {
    goto_convert.str << e;
    goto_convert.error_msg();
  }

  if(goto_convert.get_error_found())
    throw 0;
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  symbol_tablet &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler)
{
  // find main symbol
  const symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find("main");
  
  if(s_it==symbol_table.symbols.end())
    throw "failed to find main symbol";
  
  const symbolt &symbol=s_it->second;
  
  ::goto_convert(to_code(symbol.value), symbol_table, dest, message_handler);
}
