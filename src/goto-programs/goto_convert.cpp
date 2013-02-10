/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <cprover_prefix.h>
#include <expr_util.h>
#include <prefix.h>
#include <std_expr.h>
#include <symbol_table.h>
#include <simplify_expr.h>
#include <rename.h>

#include <ansi-c/c_types.h>

#include "goto_convert.h"
#include "goto_convert_class.h"
#include "destructor.h"

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
    
    if(i.code.get(ID_statement)=="non-deterministic-goto")
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
          str << "goto label " << it->id_string() << " not found";
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
        str << "goto label " << goto_label << " not found";
        throw 0;
      }

      i.targets.push_back(l_it->second);
    }
    else if(i.code.get(ID_statement)==ID_goto)
    {
      const irep_idt &goto_label=i.code.get(ID_destination);

      labelst::const_iterator l_it=targets.labels.find(goto_label);

      if(l_it==targets.labels.end())
      {
        err_location(i.code);
        str << "goto label " << goto_label << " not found";
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
      t->location=i.location;
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
  t->location=code.location();
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
    tmp_code.location()=code.location();
    convert(tmp_code, tmp);
  }
  else
    convert(to_code(code.op0()), tmp);
  
  goto_programt::targett target=tmp.instructions.begin();
  dest.destructive_append(tmp);

  if(!label.empty())
  {
    targets.labels.insert(std::pair<irep_idt, goto_programt::targett>
                          (label, target));
    target->labels.push_front(label);
  }

  // cases?

  const exprt::operandst &case_op=code.case_op();

  if(!case_op.empty())
  {
    cases_mapt::iterator cases_entry=targets.cases_map.find(target);
    if(cases_entry==targets.cases_map.end())
    {
      targets.cases.push_back(std::make_pair(target, caset()));
      cases_entry=targets.cases_map.insert(std::make_pair(
            target, --targets.cases.end())).first;
    }
    exprt::operandst &case_op_dest=cases_entry->second->second;
    
    case_op_dest.reserve(case_op_dest.size()+case_op.size());
    
    forall_expr(it, case_op)
      case_op_dest.push_back(*it);
  }

  // default?

  if(code.is_default())
    targets.set_default(target);
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
    convert_block(code, dest);
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
  else if(statement=="computed-goto")
    convert_computed_goto(code, dest);
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
  else if(statement==ID_catch) // C++ try/catch
    convert_catch(code, dest);
  else if(statement==ID_asm)
    convert_asm(code, dest);
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
  else
    copy(code, OTHER, dest);

  // make sure dest is never empty
  if(dest.instructions.empty())
  {
    dest.add_instruction(SKIP);
    dest.instructions.back().code.make_nil();
  }
}

/*******************************************************************\

Function: goto_convertt::convert_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_block(
  const codet &code,
  goto_programt &dest)
{
  // this needs to be ordered to obtain
  // the correct ordering for the destructor calls
  std::list<irep_idt> locals;
  
  forall_operands(it, code)
  {
    const codet &code=to_code(*it);

    if(code.get_statement()==ID_decl)
    {
      const exprt &op0=code.op0();
      assert(op0.id()==ID_symbol);
      const irep_idt &identifier=op0.get(ID_identifier);
      const symbolt &symbol=lookup(identifier);
      
      if(!symbol.is_static_lifetime &&
         symbol.type.id()!=ID_code)
        locals.push_back(identifier);
    }
    
    convert(code, dest);

    for(tmp_symbolst::const_iterator
        it=tmp_symbols.begin();
        it!=tmp_symbols.end();
        it++)
      locals.push_back(*it);

    tmp_symbols.clear();
  }

  // see if we need to call any destructors

  while(!locals.empty())
  {
    const symbolt &symbol=ns.lookup(locals.back());

    code_function_callt destructor=get_destructor(ns, symbol.type);

    if(destructor.is_not_nil())
    {
      // add "this"
      exprt this_expr(ID_address_of, pointer_typet());
      this_expr.type().subtype()=symbol.type;
      this_expr.copy_to_operands(symbol_expr(symbol));
      destructor.arguments().push_back(this_expr);

      convert(destructor, dest);
    }
    
    locals.pop_back();
  }
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
    // we do a special treatment for ?: 
    const if_exprt &if_expr=to_if_expr(expr);
    code_ifthenelset tmp_code;
    tmp_code.location()=expr.location();
    tmp_code.cond()=if_expr.cond();
    tmp_code.then_case()=code_expressiont(if_expr.true_case());
    tmp_code.then_case().location()=expr.location();
    tmp_code.else_case()=code_expressiont(if_expr.false_case());
    tmp_code.else_case().location()=expr.location();
    convert_ifthenelse(tmp_code, dest);
  }
  else
  {
    clean_expr(expr, dest, false); // result _not_ used

    if(expr.is_not_nil())
    {
      codet tmp=code;
      tmp.op0()=expr;
      tmp.location()=expr.location();
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
    exprt initializer;
  
    codet tmp=code;
    initializer=code.op1();
    tmp.operands().resize(1);
    
    // Break up into decl and assignment.
    // Decl must be visible before initializer.
    copy(tmp, DECL, dest);

    code_assignt assign(code.op0(), initializer);
    assign.location()=tmp.location();

    convert_assign(assign, dest);
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

  if(rhs.id()==ID_sideeffect &&
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
  else if(rhs.id()==ID_sideeffect &&
          (rhs.get(ID_statement)==ID_cpp_new ||
           rhs.get(ID_statement)=="cpp_new[]"))
  {
    Forall_operands(it, rhs)
      clean_expr(*it, dest);

    do_cpp_new(lhs, to_side_effect_expr(rhs), dest);
  }
  else if(rhs.id()==ID_sideeffect &&
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
    delete_identifier="c::__delete_array";
  else if(code.get_statement()==ID_cpp_delete)
    delete_identifier="c::__delete";
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
  exprt delete_symbol=symbol_expr(ns.lookup(delete_identifier));
  
  assert(to_code_type(delete_symbol.type()).arguments().size()==1);

  typet arg_type=
    to_code_type(delete_symbol.type()).arguments().front().type();
  
  code_function_callt delete_call;
  delete_call.function()=delete_symbol;
  delete_call.arguments().push_back(typecast_exprt(tmp_op, arg_type));
  delete_call.lhs().make_nil();
  delete_call.location()=code.location();
  
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
  t->location=code.location();
  t->location.set(ID_property, ID_assertion);
  t->location.set("user-provided", true);
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
  t->location=code.location();
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
  t->location=code.location();
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
  code_blockt block;  
  if(code.init().is_not_nil())
  {
    block.copy_to_operands(code.init());
    convert(block, dest);
  }
    
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

  // do the x label
  goto_programt tmp_x;
  
  if(code.op2().is_nil())
    tmp_x.add_instruction(SKIP);
  else
  {
    exprt tmp_B=code.iter();

    clean_expr(tmp_B, tmp_x, false);

    if(tmp_x.instructions.empty())
      tmp_x.add_instruction(SKIP);
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
  v->location=cond.location();

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w);
  
  // y: goto u;
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();
  y->make_goto(u);
  y->guard.make_true();
  y->location=code.location();

  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  targets.restore(old_targets);
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
  const locationt &location=code.location();

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

  goto_programt tmp_branch;
  generate_conditional_branch(gen_not(cond), z, location, tmp_branch);

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
  y->guard.make_true();
  y->location=code.location();

  dest.destructive_append(tmp_branch);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  targets.restore(old_targets);
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

  // save location  
  locationt condition_location=code.op0().find_location();

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
  y->location=condition_location;

  dest.destructive_append(tmp_w);
  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue targets
  targets.restore(old_targets);
}

/*******************************************************************\

Function: goto_convertt::case_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::case_guard(
  const exprt &value,
  const exprt::operandst &case_op,
  exprt &dest)
{
  dest=exprt(ID_or, typet(ID_bool));
  dest.reserve_operands(case_op.size());

  forall_expr(it, case_op)
  {
    equal_exprt eq_expr;
    eq_expr.lhs()=value;
    eq_expr.rhs()=*it;
    dest.move_to_operands(eq_expr);
  }

  assert(dest.operands().size()!=0);

  if(dest.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(dest.op0());
    dest.swap(tmp);
  }
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

  // save break/continue/default/cases targets
  break_continue_switch_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();

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
  
    exprt guard_expr;
    case_guard(argument, case_ops, guard_expr);

    goto_programt::targett x=tmp_cases.add_instruction();
    x->make_goto(it->first);
    x->guard.swap(guard_expr);
    x->location=case_ops.front().find_location();
  }

  {
    goto_programt::targett d_jump=tmp_cases.add_instruction();
    d_jump->make_goto(targets.default_target);
    d_jump->location=targets.default_target->location;
  }

  dest.destructive_append(sideeffects);
  dest.destructive_append(tmp_cases);
  dest.destructive_append(tmp);
  dest.destructive_append(tmp_z);

  // restore old targets
  targets.restore(old_targets);
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

  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.break_target);
  t->location=code.location();
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
  if(!targets.return_is_set)
  {
    err_location(code);
    throw "return without target";
  }

  if(code.operands().size()!=0 &&
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

  goto_programt::targett t=dest.add_instruction();
  t->make_return();
  t->code=new_code;
  t->location=new_code.location();
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

  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.continue_target);
  t->location=code.location();
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
  t->location=code.location();
  t->code=code;

  // remember it to do target later
  targets.gotos.push_back(t);
}

/*******************************************************************\

Function: goto_convertt::convert_computed_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_computed_goto(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction();
  t->make_skip();
  t->location=code.location();
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
  t->location=code.location();
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
  t->location=code.location();
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

  start_thread->location=code.location();
  
  // see if op0 is an unconditional goto
  
  if(code.op0().get(ID_statement)==ID_goto)
  {
    start_thread->code.set(ID_destination,
      code.op0().get(ID_destination));
      
    // remember it to do target later
    targets.gotos.push_back(start_thread);
  }
  else
  {
    // start_thread label;
    // goto tmp;
    // label: op0-code
    // end_thread
    // tmp: skip
    
    goto_programt::targett goto_instruction=dest.add_instruction(GOTO);
    goto_instruction->guard=true_exprt();
    goto_instruction->location=code.location();

    goto_programt tmp;
    convert(to_code(code.op0()), tmp);
    goto_programt::targett end_thread=tmp.add_instruction(END_THREAD);
    end_thread->location=code.location();
    
    start_thread->targets.push_back(tmp.instructions.begin());
    dest.destructive_append(tmp);
    goto_instruction->targets.push_back(dest.add_instruction(SKIP));
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
  if(code.operands().size()!=0)
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
  if(code.operands().size()!=0)
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
  if(code.operands().size()!=0)
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
    error("bp_enfroce expects two arguments");
    throw 0;
  }
    
  // do an assume
  exprt op=code.op0();

  clean_expr(op, dest);

  goto_programt::targett t=dest.add_instruction(ASSUME);
  t->guard=op;
  t->location=code.location();

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
  t->location=code.location();
}

/*******************************************************************\

Function: goto_convertt::convert_msc_try_finally

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_try_finally(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "msc_try_finally expects two arguments";
  }

  convert(to_code(code.op0()), dest);
  
  // todo: generate exception tracking
}

/*******************************************************************\

Function: goto_convertt::convert_msc_try_except

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_try_except(
  const codet &code,
  goto_programt &dest)
{
  if(code.operands().size()!=3)
  {
    err_location(code);
    throw "msc_try_except expects three arguments";
  }

  convert(to_code(code.op0()), dest);
  
  // todo: generate exception tracking
}

/*******************************************************************\

Function: goto_convertt::convert_msc_leave

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_msc_leave(
  const codet &code,
  goto_programt &dest)
{
  // todo: should throw (silent) exception
}

/*******************************************************************\

Function: goto_convertt::convert_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_catch(
  const codet &code,
  goto_programt &dest)
{
  assert(code.operands().size()>=2);
  
  // add the CATCH-push instruction to 'dest'
  goto_programt::targett catch_push_instruction=dest.add_instruction();
  catch_push_instruction->make_catch();
  catch_push_instruction->code.set_statement(ID_catch);
  catch_push_instruction->location=code.location();
  
  // the CATCH-push instruction is annotated with a list of IDs,
  // one per target
  irept::subt &exception_list=
    catch_push_instruction->code.add(ID_exception_list).get_sub();

  // add a SKIP target for the end of everything
  goto_programt end;
  goto_programt::targett end_target=end.add_instruction();
  end_target->make_skip();
  
  // the first operand is the 'try' block
  convert(to_code(code.op0()), dest);
  
  // add the CATCH-pop to the end of the 'try' block
  goto_programt::targett catch_pop_instruction=dest.add_instruction();
  catch_pop_instruction->make_catch();
  catch_pop_instruction->code.set_statement(ID_catch);
  
  // add a goto to the end of the 'try' block
  dest.add_instruction()->make_goto(end_target);

  for(unsigned i=1; i<code.operands().size(); i++)
  {
    const codet &block=to_code(code.operands()[i]);
  
    // grab the ID and add to CATCH instruction
    exception_list.push_back(irept(block.get(ID_exception_id)));
    
    goto_programt tmp;
    convert(block, tmp);
    catch_push_instruction->targets.push_back(tmp.instructions.begin());
    dest.destructive_append(tmp);

    // add a goto to the end of the 'catch' block
    dest.add_instruction()->make_goto(end_target);
  }

  // add end-target  
  dest.destructive_append(end);
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

  const locationt &location=code.location();

  // we do a bit of special treatment for && in the condition
  // in case cleaning would be needed otherwise
  if(code.cond().id()==ID_and &&
     code.cond().operands().size()==2 &&
     (needs_cleaning(code.cond().op0()) || needs_cleaning(code.cond().op1())) &&
     !has_else)
  {
    // if(a && b) XX --> if(a) if(b) XX
    code_ifthenelset new_if0, new_if1;
    new_if0.cond()=code.cond().op0();
    new_if1.cond()=code.cond().op1();
    new_if0.location()=location;
    new_if1.location()=location;
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

  generate_ifthenelse(tmp_guard, tmp_then, tmp_else, location, dest);
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

 Purpose: if(guard) goto target;

\*******************************************************************/

void goto_convertt::generate_ifthenelse(
  const exprt &guard,
  goto_programt &true_case,
  goto_programt &false_case,
  const locationt &location,
  goto_programt &dest)
{
  if(true_case.instructions.empty() &&
     false_case.instructions.empty())
    return;

  // do guarded gotos directly
  if(false_case.instructions.empty() &&
     true_case.instructions.size()==1 &&
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

  if(true_case.instructions.empty())
    return generate_ifthenelse(
      gen_not(guard), false_case, true_case, location, dest);

  bool has_else=!false_case.instructions.empty();

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
    gen_not(guard), has_else?y:z, location, tmp_v);

  // w: P;
  goto_programt tmp_w;
  tmp_w.swap(true_case);

  // x: goto z;
  x->make_goto(z);

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
  const locationt &location,
  goto_programt &dest)
{
  if(has_and_or(guard))
  {
    // if(guard) goto target;
    //   becomes
    // if(guard) goto target; else goto next;
    // next: skip;

    goto_programt tmp;
    goto_programt::targett target_false=tmp.add_instruction();
    target_false->make_skip();
    
    generate_conditional_branch(
      guard, target_true, target_false, location, dest);
    
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
    g->location=location;
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
  const locationt &location,
  goto_programt &dest)
{
  if(guard.id()==ID_not)
  {
    assert(guard.operands().size()==1);
    // simply swap targets
    generate_conditional_branch(
      guard.op0(), target_false, target_true, location, dest);
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
        gen_not(*it), target_false, location, dest);

    goto_programt::targett t_true=dest.add_instruction();
    t_true->make_goto(target_true);
    t_true->guard=true_exprt();
    t_true->location=location;
    
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
        *it, target_true, location, dest);

    goto_programt::targett t_false=dest.add_instruction();
    t_false->make_goto(target_false);
    t_false->guard=true_exprt();
    t_false->location=guard.location();
    
    return;
  }

  exprt cond=guard;
  clean_expr(cond, dest);
  
  goto_programt::targett t_true=dest.add_instruction();
  t_true->make_goto(target_true);
  t_true->guard=cond;
  t_true->location=location;

  goto_programt::targett t_false=dest.add_instruction();
  t_false->make_goto(target_false);
  t_false->guard=true_exprt();
  t_false->location=location;
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
  error();

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
  const locationt &location)
{
  symbolt new_symbol;
  symbolt *symbol_ptr;
  
  do
  {
    new_symbol.base_name="tmp_"+suffix+"$"+i2string(++temporary_counter);
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);
    new_symbol.is_lvalue=true;
    new_symbol.is_thread_local=true;
    new_symbol.is_file_local=true;
    new_symbol.type=type;    
  } while(symbol_table.move(new_symbol, symbol_ptr));    
  
  tmp_symbols.push_back(symbol_ptr->name);
  
  goto_programt::targett t=dest.add_instruction(DECL);
  t->code=code_declt(symbol_expr(*symbol_ptr));
  t->location=location;

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
  const locationt location=expr.find_location();
  
  symbolt &new_symbol=
    new_tmp_symbol(expr.type(), suffix, dest, location);

  code_assignt assignment;
  assignment.lhs()=symbol_expr(new_symbol);
  assignment.rhs()=expr;
  assignment.location()=location;

  convert(assignment, dest);

  expr=symbol_expr(new_symbol);  
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
    goto_convert.error();
  }

  catch(const char *e)
  {
    goto_convert.error(e);
  }

  catch(const std::string &e)
  {
    goto_convert.error(e);
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
