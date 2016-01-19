/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/config.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/type_eq.h>
#include <util/i2string.h>

#include "goto_program2code.h"

/*******************************************************************\

Function: skip_typecast

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static const exprt& skip_typecast(const exprt &expr)
{
  if(expr.id()!=ID_typecast)
    return expr;

  return skip_typecast(to_typecast_expr(expr).op());
}

/*******************************************************************\

Function: goto_program2codet::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::operator()()
{
  // labels stored for cleanup
  labels_in_use.clear();

  // just an estimate
  toplevel_block.reserve_operands(goto_program.instructions.size());

  // find loops first
  build_loop_map();

  // gather variable scope information
  build_dead_map();

  // see whether var args are in use, identify va_list symbol
  scan_for_varargs();

  // convert
  forall_goto_program_instructions(target, goto_program)
    target=convert_instruction(
        target,
        goto_program.instructions.end(),
        toplevel_block);

  cleanup_code(toplevel_block, ID_nil);
}

/*******************************************************************\

Function: goto_program2codet::build_loop_map

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::build_loop_map()
{
  loop_map.clear();
  loops.loop_map.clear();
  loops(goto_program);

  for(natural_loopst::loop_mapt::const_iterator
      l_it=loops.loop_map.begin();
      l_it!=loops.loop_map.end();
      ++l_it)
  {
    assert(!l_it->second.empty());

    // l_it->first need not be the program-order first instruction in the
    // natural loop, because a natural loop may have multiple entries. But we
    // ignore all those before l_it->first
    // Furthermore the loop may contain code after the source of the actual back
    // edge -- we also ignore such code
    goto_programt::const_targett loop_start=l_it->first;
    goto_programt::const_targett loop_end=loop_start;
    for(natural_loopst::natural_loopt::const_iterator
        it=l_it->second.begin();
        it!=l_it->second.end();
        ++it)
      if((*it)->is_goto())
      {
        if((*it)->get_target()==loop_start &&
            (*it)->location_number>loop_end->location_number)
          loop_end=*it;
      }

    if(!loop_map.insert(std::make_pair(loop_start, loop_end)).second)
      assert(false);
  }
}

/*******************************************************************\

Function: goto_program2codet::build_dead_map

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::build_dead_map()
{
  dead_map.clear();

  // record last dead X
  forall_goto_program_instructions(target, goto_program)
    if(target->is_dead())
      dead_map[to_code_dead(target->code).get_identifier()]=
        target->location_number;
}

/*******************************************************************\

Function: goto_program2codet::scan_for_varargs

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::scan_for_varargs()
{
  va_list_expr.clear();

  forall_goto_program_instructions(target, goto_program)
    if(target->is_assign())
    {
      const exprt &r=to_code_assign(target->code).rhs();

      if(r.id()==ID_side_effect &&
         to_side_effect_expr(r).get_statement()==ID_gcc_builtin_va_arg_next)
      {
        assert(r.has_operands());
        va_list_expr.insert(r.op0());
      }
    }

  if(!va_list_expr.empty())
  {
    system_headers.insert("stdarg.h");

    symbol_tablet::symbolst::iterator it=
      symbol_table.symbols.find(func_name);
    assert(it!=symbol_table.symbols.end());

    code_typet &code_type=to_code_type(it->second.type);
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it2=parameters.begin();
        it2!=parameters.end();
        ++it2)
    {
      const symbol_exprt arg=
        ns.lookup(it2->get_identifier()).symbol_expr();
      if(va_list_expr.find(arg)!=va_list_expr.end())
        it2->type().id(ID_gcc_builtin_va_list);
    }
  }
}

/*******************************************************************\

Function: goto_program2codet::convert_instruction

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_instruction(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  assert(target!=goto_program.instructions.end());

  if(target->type!=ASSERT &&
     !target->source_location.get_comment().empty())
  {
    dest.copy_to_operands(code_skipt());
    dest.operands().back().add_source_location().set_comment(
      target->source_location.get_comment());
  }

  // try do-while first
  if(target->is_target() && !target->is_goto())
  {
    loopt::const_iterator loop_entry=loop_map.find(target);

    if(loop_entry!=loop_map.end() &&
        (upper_bound==goto_program.instructions.end() ||
         upper_bound->location_number > loop_entry->second->location_number))
      return convert_do_while(target, loop_entry->second, dest);
  }

  convert_labels(target, dest);

  switch(target->type)
  {
    case SKIP:
    case LOCATION:
    case END_FUNCTION:
    case DEAD:
      // ignore for now
      dest.copy_to_operands(code_skipt());
      return target;

    case FUNCTION_CALL:
    case OTHER:
      dest.copy_to_operands(target->code);
      return target;

    case ASSIGN:
      return convert_assign(target, upper_bound, dest);

    case RETURN:
      return convert_return(target, upper_bound, dest);

    case DECL:
      return convert_decl(target, upper_bound, dest);

    case ASSERT:
      system_headers.insert("assert.h");
      dest.copy_to_operands(code_assertt(target->guard));
      dest.operands().back().add_source_location().set_comment(
          target->source_location.get_comment());
      return target;

    case ASSUME:
      dest.copy_to_operands(code_assumet(target->guard));
      return target;

    case GOTO:
      return convert_goto(target, upper_bound, dest);

    case START_THREAD:
      return convert_start_thread(target, upper_bound, dest);

    case END_THREAD:
      dest.copy_to_operands(code_assumet(false_exprt()));
      dest.operands().back().add_source_location().set_comment("END_THREAD");
      return target;

    case ATOMIC_BEGIN:
    case ATOMIC_END:
      {
        code_function_callt f;
        code_typet void_t;
        void_t.return_type()=empty_typet();
        f.function()=symbol_exprt(
            target->is_atomic_begin() ?
            "__CPROVER_atomic_begin" :
            "__CPROVER_atomic_end",
            void_t);
        dest.move_to_operands(f);
        return target;
      }

    case THROW:
      return convert_throw(target, dest);

    case CATCH:
      return convert_catch(target, upper_bound, dest);

    case NO_INSTRUCTION_TYPE:
      assert(false);
  }

  // not reached
  assert(false);
  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_labels

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::convert_labels(
    goto_programt::const_targett target,
    codet &dest)
{
  codet *latest_block=&dest;

  irep_idt target_label;
  if(target->is_target())
  {
    std::stringstream label;
    label << "__CPROVER_DUMP_L" << target->target_number;
    code_labelt l(label.str(), code_blockt());
    l.add_source_location()=target->source_location;
    target_label=l.get_label();
    latest_block->move_to_operands(l);
    latest_block=&to_code_label(
        to_code(latest_block->operands().back())).code();
  }

  for(goto_programt::instructiont::labelst::const_iterator
      it=target->labels.begin();
      it!=target->labels.end();
      ++it)
  {
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_") ||
        has_prefix(id2string(*it), "__CPROVER_DUMP_L"))
      continue;

    // keep all original labels
    labels_in_use.insert(*it);

    code_labelt l(*it, code_blockt());
    l.add_source_location()=target->source_location;
    latest_block->move_to_operands(l);
    latest_block=&to_code_label(
        to_code(latest_block->operands().back())).code();
  }

  if(latest_block!=&dest)
    latest_block->copy_to_operands(code_skipt());
}

/*******************************************************************\

Function: goto_program2codet::convert_assign

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_assign(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  const code_assignt &a=to_code_assign(target->code);

  if(va_list_expr.find(a.lhs())!=va_list_expr.end())
    return convert_assign_varargs(target, upper_bound, dest);
  else
    convert_assign_rec(a, dest);

  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_assign_varargs

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_assign_varargs(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  const code_assignt &assign=to_code_assign(target->code);

  const exprt this_va_list_expr=assign.lhs();
  const exprt &r=skip_typecast(assign.rhs());

  // we don't bother setting the type
  code_function_callt f;
  f.lhs().make_nil();

  if(r.id()==ID_constant &&
     (r.is_zero() || to_constant_expr(r).get_value()==ID_NULL))
  {
    f.function()=symbol_exprt("va_end", code_typet());
    f.arguments().push_back(this_va_list_expr);
    f.arguments().back().type().id(ID_gcc_builtin_va_list);

    dest.move_to_operands(f);
  }
  else if(r.id()==ID_address_of)
  {
    f.function()=symbol_exprt("va_start", code_typet());
    f.arguments().push_back(this_va_list_expr);
    f.arguments().back().type().id(ID_gcc_builtin_va_list);
    f.arguments().push_back(to_address_of_expr(r).object());

    dest.move_to_operands(f);
  }
  else if(r.id()==ID_side_effect &&
          to_side_effect_expr(r).get_statement()==ID_gcc_builtin_va_arg_next)
  {
    f.function()=symbol_exprt("va_arg", code_typet());
    f.arguments().push_back(this_va_list_expr);
    f.arguments().back().type().id(ID_gcc_builtin_va_list);

    side_effect_expr_function_callt type_of;
    type_of.function()=symbol_exprt("__typeof__", code_typet());

    // if the return value is used, the next instruction will be assign
    goto_programt::const_targett next=target;
    ++next;
    assert(next!=goto_program.instructions.end());
    if(next!=upper_bound &&
       next->is_assign())
    {
       const exprt &n_r=to_code_assign(next->code).rhs();
       if(n_r.id()==ID_dereference &&
          skip_typecast(to_dereference_expr(n_r).pointer())==
          this_va_list_expr)
       {
         f.lhs()=to_code_assign(next->code).lhs();

         type_of.arguments().push_back(f.lhs());
         f.arguments().push_back(type_of);

         dest.move_to_operands(f);
         return next;
       }
    }

    // assignment not found, still need a proper typeof expression
    assert(r.find(ID_C_va_arg_type).is_not_nil());
    const typet &va_arg_type=
      static_cast<typet const&>(r.find(ID_C_va_arg_type));

    dereference_exprt deref(
      typecast_exprt(
        from_integer(0, signedbv_typet(config.ansi_c.pointer_width)),
        pointer_typet(va_arg_type)),
      va_arg_type);

    type_of.arguments().push_back(deref);
    f.arguments().push_back(type_of);

    code_expressiont void_f(typecast_exprt(f, empty_typet()));

    dest.move_to_operands(void_f);
  }
  else
  {
    f.function()=symbol_exprt("va_copy", code_typet());
    f.arguments().push_back(this_va_list_expr);
    f.arguments().back().type().id(ID_gcc_builtin_va_list);
    f.arguments().push_back(r);

    dest.move_to_operands(f);
  }

  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_assign_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::convert_assign_rec(
    const code_assignt &assign,
    codet &dest)
{
  if(assign.rhs().id()==ID_array)
  {
    const array_typet &type=
      to_array_type(ns.follow(assign.rhs().type()));

    unsigned i=0;
    forall_operands(it, assign.rhs())
    {
      index_exprt index(
          assign.lhs(),
          from_integer(i++, signedbv_typet(config.ansi_c.pointer_width)),
          type.subtype());
      convert_assign_rec(code_assignt(index, *it), dest);
    }
  }
  else
    dest.copy_to_operands(assign);
}

/*******************************************************************\

Function: goto_program2codet::convert_return

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_return(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  code_returnt ret=to_code_return(target->code);

  // add return instruction unless original code was missing a return
  if(!ret.has_return_value() ||
     ret.return_value().id()!=ID_side_effect ||
     to_side_effect_expr(ret.return_value()).get_statement()!=ID_nondet)
    dest.copy_to_operands(ret);

  // all v3 (or later) goto programs have an explicit GOTO after return
  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());

  // skip goto (and possibly dead), unless crossing the current boundary
  while(next!=upper_bound && next->is_dead() && !next->is_target())
    ++next;

  if(next!=upper_bound &&
     next->is_goto() &&
     !next->is_target())
    target=next;

  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_decl

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_decl(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  code_declt d=to_code_decl(target->code);
  symbol_exprt &symbol=to_symbol_expr(d.symbol());

  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());

  // see if decl can go in current dest block
  dead_mapt::const_iterator entry=dead_map.find(symbol.get_identifier());
  bool move_to_dest= &toplevel_block==&dest ||
    (entry!=dead_map.end() &&
     upper_bound->location_number > entry->second);

  // move back initialising assignments into the decl, unless crossing the
  // current boundary
  if(next!=upper_bound &&
     move_to_dest &&
     !next->is_target() &&
     next->is_assign())
  {
    const code_assignt &a=to_code_assign(next->code);
    if(a.lhs()==symbol &&
       va_list_expr.find(a.lhs())==va_list_expr.end())
    {
      d.copy_to_operands(a.rhs());

      ++target;
      convert_labels(target, dest);
    }
    else
      remove_const(symbol.type());
  }
  // if we have a constant but can't initialize them right away, we need to
  // remove the const marker
  else
    remove_const(symbol.type());

  if(move_to_dest)
    dest.move_to_operands(d);
  else
    toplevel_block.move_to_operands(d);

  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_do_while

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_do_while(
    goto_programt::const_targett target,
    goto_programt::const_targett loop_end,
    codet &dest)
{
  assert(loop_end->is_goto() && loop_end->is_backwards_goto());

  code_dowhilet d;
  d.cond()=loop_end->guard;
  simplify(d.cond(), ns);
  d.body()=code_blockt();

  loop_last_stack.push_back(std::make_pair(loop_end, true));

  for( ; target!=loop_end; ++target)
    target=convert_instruction(target, loop_end, d.body());

  loop_last_stack.pop_back();

  convert_labels(loop_end, d.body());

  dest.move_to_operands(d);
  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_goto

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  assert(target->is_goto());
  // we only do one target for now
  assert(target->targets.size()==1);

  loopt::const_iterator loop_entry=loop_map.find(target);

  if(loop_entry!=loop_map.end() &&
      (upper_bound==goto_program.instructions.end() ||
       upper_bound->location_number > loop_entry->second->location_number))
    return convert_goto_while(target, loop_entry->second, dest);
  else if(!target->guard.is_true())
    return convert_goto_switch(target, upper_bound, dest);
  else if(!loop_last_stack.empty())
    return convert_goto_break_continue(target, dest);
  else
    return convert_goto_goto(target, dest);
}

/*******************************************************************\

Function: goto_program2codet::convert_goto_while

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_while(
    goto_programt::const_targett target,
    goto_programt::const_targett loop_end,
    codet &dest)
{
  assert(loop_end->is_goto() && loop_end->is_backwards_goto());

  if(target==loop_end) // 1: GOTO 1
    return convert_goto_goto(target, dest);

  code_whilet w;
  w.body()=code_blockt();
  goto_programt::const_targett after_loop=loop_end;
  ++after_loop;
  assert(after_loop!=goto_program.instructions.end());
  if(target->get_target()==after_loop)
  {
    w.cond()=not_exprt(target->guard);
    simplify(w.cond(), ns);
  }
  else if(target->guard.is_true())
  {
    w.cond()=true_exprt();
    target=convert_goto_goto(target, w.body());
  }
  else
  {
    w.cond()=true_exprt();
    target=convert_goto_switch(target, loop_end, w.body());
  }

  loop_last_stack.push_back(std::make_pair(loop_end, true));

  for(++target; target!=loop_end; ++target)
    target=convert_instruction(target, loop_end, w.body());

  loop_last_stack.pop_back();

  convert_labels(loop_end, w.body());
  if(loop_end->guard.is_false())
  {
    code_breakt brk;

    w.body().move_to_operands(brk);
  }
  else if(!loop_end->guard.is_true())
  {
    code_ifthenelset i;

    i.cond()=not_exprt(loop_end->guard);
    simplify(i.cond(), ns);
    i.then_case()=code_breakt();

    w.body().move_to_operands(i);
  }

  if(w.body().has_operands() &&
     to_code(w.body().operands().back()).get_statement()==ID_assign)
  {
    code_fort f;

    f.init().make_nil();

    f.cond()=w.cond();

    f.iter()=w.body().operands().back();
    w.body().operands().pop_back();
    f.iter().id(ID_side_effect);

    f.body().swap(w.body());

    f.swap(w);
  }
  else if(w.body().has_operands() &&
          w.cond().is_true())
  {
    const codet &back=to_code(w.body().operands().back());

    if(back.get_statement()==ID_break ||
       (back.get_statement()==ID_ifthenelse &&
        to_code_ifthenelse(back).cond().is_true() &&
        to_code_ifthenelse(back).then_case().get_statement()==ID_break))
    {
      code_dowhilet d;

      d.cond()=false_exprt();

      w.body().operands().pop_back();
      d.body().swap(w.body());

      d.swap(w);
    }
  }

  dest.move_to_operands(w);

  return target;
}

/*******************************************************************\

Function: goto_program2codet::get_cases

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::get_cases(
  goto_programt::const_targett target,
  goto_programt::const_targett upper_bound,
  const exprt &switch_var,
  cases_listt &cases,
  goto_programt::const_targett &first_target,
  goto_programt::const_targett &default_target)
{
  goto_programt::const_targett last_target=goto_program.instructions.end();
  std::set<goto_programt::const_targett> unique_targets;

  goto_programt::const_targett cases_it=target;
  for( ;
      cases_it!=upper_bound && cases_it!=first_target;
      ++cases_it)
  {
    if(cases_it->is_goto() &&
       !cases_it->is_backwards_goto() &&
       cases_it->guard.is_true())
    {
      default_target=cases_it->get_target();

      if(first_target==goto_program.instructions.end() ||
         first_target->location_number > default_target->location_number)
        first_target=default_target;
      if(last_target==goto_program.instructions.end() ||
         last_target->location_number < default_target->location_number)
        last_target=default_target;

      cases.push_back(caset(
          goto_program,
          nil_exprt(),
          cases_it,
          default_target));
      unique_targets.insert(default_target);

      ++cases_it;
      break;
    }
    else if(cases_it->is_goto() &&
            !cases_it->is_backwards_goto() &&
            (cases_it->guard.id()==ID_equal ||
             cases_it->guard.id()==ID_or))
    {
      exprt::operandst eqs;
      if(cases_it->guard.id()==ID_equal)
        eqs.push_back(cases_it->guard);
      else
        eqs=cases_it->guard.operands();

      // goto conversion builds disjunctions in reverse order
      // to ensure convergence, we turn this around again
      for(exprt::operandst::const_reverse_iterator
          e_it=eqs.rbegin();
          e_it!=(exprt::operandst::const_reverse_iterator)eqs.rend();
          ++e_it)
      {
        if(e_it->id()!=ID_equal ||
           !skip_typecast(to_equal_expr(*e_it).rhs()).is_constant() ||
           switch_var!=to_equal_expr(*e_it).lhs())
          return target;

        cases.push_back(caset(
            goto_program,
            to_equal_expr(*e_it).rhs(),
            cases_it,
            cases_it->get_target()));
        assert(cases.back().value.is_not_nil());

        if(first_target==goto_program.instructions.end() ||
           first_target->location_number > cases.back().case_start->location_number)
          first_target=cases.back().case_start;
        if(last_target==goto_program.instructions.end() ||
           last_target->location_number < cases.back().case_start->location_number)
          last_target=cases.back().case_start;

        unique_targets.insert(cases.back().case_start);
      }
    }
    else
      return target;
  }

  // if there are less than 3 targets, we revert to if/else instead; this should
  // help convergence
  if(unique_targets.size()<3)
    return target;

  // make sure we don't have some overlap of gotos and switch/case
  if(cases_it==upper_bound ||
     (upper_bound!=goto_program.instructions.end() &&
      upper_bound->location_number < last_target->location_number) ||
     (last_target!=goto_program.instructions.end() &&
      last_target->location_number > default_target->location_number) ||
     target->get_target()==default_target)
    return target;

  return cases_it;
}

/*******************************************************************\

Function: goto_program2codet::set_block_end_points

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool goto_program2codet::set_block_end_points(
  goto_programt::const_targett upper_bound,
  const cfg_dominatorst &dominators,
  cases_listt &cases,
  std::set<unsigned> &processed_locations)
{
  std::map<goto_programt::const_targett, unsigned> targets_done;

  for(cases_listt::iterator it=cases.begin();
      it!=cases.end();
      ++it)
  {
    // some branch targets may be shared by multiple branch instructions,
    // as in case 1: case 2: code; we build a nested code_switch_caset
    if(targets_done.find(it->case_start)!=targets_done.end())
      continue;

    // compute the block that belongs to this case
    for(goto_programt::const_targett case_end=it->case_start;
        case_end!=goto_program.instructions.end() &&
        case_end->type!=END_FUNCTION &&
        case_end!=upper_bound;
        ++case_end)
    {
      cfg_dominatorst::cfgt::entry_mapt::const_iterator i_entry=
        dominators.cfg.entry_map.find(case_end);
      assert(i_entry!=dominators.cfg.entry_map.end());
      const cfg_dominatorst::cfgt::nodet &n=
        dominators.cfg[i_entry->second];

      // ignore dead instructions for the following checks
      if(n.dominators.empty())
        continue;

      // find the last instruction dominated by the case start
      if(n.dominators.find(it->case_start)==n.dominators.end())
        break;

      if(!processed_locations.insert(case_end->location_number).second)
        assert(false);

      it->case_last=case_end;
    }

    targets_done[it->case_start]=1;
  }

  return false;
}

/*******************************************************************\

Function: goto_program2codet::remove_default

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool goto_program2codet::remove_default(
  const cfg_dominatorst &dominators,
  const cases_listt &cases,
  goto_programt::const_targett default_target)
{
  for(cases_listt::const_iterator it=cases.begin();
      it!=cases.end();
      ++it)
  {
    // ignore empty cases
    if(it->case_last==goto_program.instructions.end()) continue;

    // the last case before default is the most interesting
    cases_listt::const_iterator last=--cases.end();
    if(last->case_start==default_target &&
       it==--last)
    {
      // ignore dead instructions for the following checks
      goto_programt::const_targett next_case=it->case_last;
      for(++next_case;
          next_case!=goto_program.instructions.end();
          ++next_case)
      {
        cfg_dominatorst::cfgt::entry_mapt::const_iterator i_entry=
          dominators.cfg.entry_map.find(next_case);
        assert(i_entry!=dominators.cfg.entry_map.end());
        const cfg_dominatorst::cfgt::nodet &n=
          dominators.cfg[i_entry->second];

        if(!n.dominators.empty())
          break;
      }

      if(next_case!=goto_program.instructions.end() &&
         next_case==default_target &&
         (!it->case_last->is_goto() ||
          (it->case_last->guard.is_true() &&
           it->case_last->get_target()==default_target)))
      {
        // if there is no goto here, yet we got here, all others would
        // branch to this - we don't need default
        return true;
      }
    }

    // jumps to default are ok
    if(it->case_last->is_goto() &&
       it->case_last->guard.is_true() &&
       it->case_last->get_target()==default_target)
      continue;

    // fall-through is ok
    if(!it->case_last->is_goto()) continue;

    return false;
  }

  return false;
}

/*******************************************************************\

Function: goto_program2codet::convert_goto_switch

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_switch(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  // try to figure out whether this was a switch/case
  exprt eq_cand=target->guard;
  if(eq_cand.id()==ID_or) eq_cand=eq_cand.op0();

  if(target->is_backwards_goto() ||
     eq_cand.id()!=ID_equal ||
     !skip_typecast(to_equal_expr(eq_cand).rhs()).is_constant())
    return convert_goto_if(target, upper_bound, dest);

  const cfg_dominatorst &dominators=loops.get_dominator_info();

  // always use convert_goto_if for dead code as the construction below relies
  // on effective dominator information 
  cfg_dominatorst::cfgt::entry_mapt::const_iterator t_entry=
    dominators.cfg.entry_map.find(target);
  assert(t_entry!=dominators.cfg.entry_map.end());
  if(dominators.cfg[t_entry->second].dominators.empty())
    return convert_goto_if(target, upper_bound, dest);

  // maybe, let's try some more
  code_switcht s;
  s.value()=to_equal_expr(eq_cand).lhs();
  s.body()=code_blockt();

  // find the cases or fall back to convert_goto_if
  cases_listt cases;
  goto_programt::const_targett first_target=
    goto_program.instructions.end();
  goto_programt::const_targett default_target=
    goto_program.instructions.end();

  goto_programt::const_targett cases_start=
    get_cases(
      target,
      upper_bound,
      s.value(),
      cases,
      first_target,
      default_target);

  if(cases_start==target)
    return convert_goto_if(target, upper_bound, dest);

  // backup the top-level block as we might have to backtrack
  code_blockt toplevel_block_bak=toplevel_block;

  // add any instructions that go in the body of the switch before any cases
  goto_programt::const_targett orig_target=target;
  for(target=cases_start; target!=first_target; ++target)
    target=convert_instruction(target, first_target, s.body());

  std::set<unsigned> processed_locations;

  // iterate over all cases to identify block end points
  if(set_block_end_points(upper_bound, dominators, cases, processed_locations))
  {
    toplevel_block.swap(toplevel_block_bak);
    return convert_goto_if(orig_target, upper_bound, dest);
  }

  // figure out whether we really had a default target by testing
  // whether all cases eventually jump to the default case
  if(remove_default(dominators, cases, default_target))
  {
    cases.pop_back();
    default_target=goto_program.instructions.end();
  }

  // find the last instruction belonging to any of the cases
  goto_programt::const_targett max_target=target;
  for(cases_listt::const_iterator it=cases.begin();
      it!=cases.end();
      ++it)
    if(it->case_last!=goto_program.instructions.end() &&
       it->case_last->location_number > max_target->location_number)
      max_target=it->case_last;

  std::map<goto_programt::const_targett, unsigned> targets_done;
  loop_last_stack.push_back(std::make_pair(max_target, false));

  // iterate over all <branch conditions, branch instruction, branch target>
  // triples, build their corresponding code
  for(cases_listt::const_iterator it=cases.begin();
      it!=cases.end();
      ++it)
  {
    code_switch_caset csc;
    // branch condition is nil_exprt for default case;
    if(it->value.is_nil())
      csc.set_default();
    else
      csc.case_op()=it->value;

    // some branch targets may be shared by multiple branch instructions,
    // as in case 1: case 2: code; we build a nested code_switch_caset
    if(targets_done.find(it->case_start)!=targets_done.end())
    {
      assert(it->case_selector==orig_target ||
             !it->case_selector->is_target());

      // maintain the order to ensure convergence -> go to the innermost
      code_switch_caset *cscp=&to_code_switch_case(
        to_code(s.body().operands()[targets_done[it->case_start]]));
      while(cscp->code().get_statement()==ID_switch_case)
        cscp=&to_code_switch_case(cscp->code());

      csc.code().swap(cscp->code());
      cscp->code().swap(csc);

      continue;
    }

    code_blockt c;
    if(it->case_selector!=orig_target)
      convert_labels(it->case_selector, c);

    // convert the block that belongs to this case
    target=it->case_start;

    // empty case
    if(it->case_last==goto_program.instructions.end())
    {
      // only emit the jump out of the switch if it's not the last case
      // this improves convergence
      if(it->case_start!=(--cases.end())->case_start)
      {
        assert(false);
        goto_programt::instructiont i=*(it->case_selector);
        i.guard=true_exprt();
        goto_programt tmp;
        tmp.insert_before_swap(tmp.insert_before(tmp.instructions.end()), i);
        convert_goto_goto(tmp.instructions.begin(), c);
      }
    }
    else
    {
      goto_programt::const_targett after_last=it->case_last;
      ++after_last;
      for( ; target!=after_last; ++target)
        target=convert_instruction(target, after_last, c);
    }

    csc.code().swap(c);
    targets_done[it->case_start]=s.body().operands().size();
    s.body().move_to_operands(csc);
  }

  loop_last_stack.pop_back();

  // make sure we didn't miss any non-dead instruction
  for(goto_programt::const_targett it=first_target;
      it!=target;
      ++it)
    if(processed_locations.find(it->location_number)==
        processed_locations.end())
    {
      cfg_dominatorst::cfgt::entry_mapt::const_iterator it_entry=
        dominators.cfg.entry_map.find(it);
      assert(it_entry!=dominators.cfg.entry_map.end());
      const cfg_dominatorst::cfgt::nodet &n=
        dominators.cfg[it_entry->second];

      if(!n.dominators.empty())
      {
        toplevel_block.swap(toplevel_block_bak);
        return convert_goto_if(orig_target, upper_bound, dest);
      }
    }

  dest.move_to_operands(s);
  return max_target;
}

/*******************************************************************\

Function: goto_program2codet::convert_goto_if

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_if(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  goto_programt::const_targett else_case=target->get_target();
  goto_programt::const_targett before_else=else_case;
  goto_programt::const_targett end_if=target->get_target();
  assert(end_if!=goto_program.instructions.end());
  bool has_else=false;

  if(!target->is_backwards_goto())
  {
    assert(else_case!=goto_program.instructions.begin());
    --before_else;

    // goto 1
    // 1: ...
    if(before_else==target)
    {
      dest.copy_to_operands(code_skipt());
      return target;
    }

    has_else=before_else->is_goto() &&
      before_else->get_target()->location_number > end_if->location_number &&
      before_else->guard.is_true() &&
      (upper_bound==goto_program.instructions.end() ||
       upper_bound->location_number >= before_else->get_target()->location_number);

    if(has_else)
      end_if=before_else->get_target();
  }

  code_ifthenelset i;
  i.then_case()=code_blockt();

  // some nesting of loops and branches we might not be able to deal with
  if(target->is_backwards_goto() ||
      (upper_bound!=goto_program.instructions.end() &&
       upper_bound->location_number < end_if->location_number))
  {
    if(!loop_last_stack.empty())
      return convert_goto_break_continue(target, dest);
    else
      return convert_goto_goto(target, dest);
  }

  i.cond()=not_exprt(target->guard);
  simplify(i.cond(), ns);

  if(has_else)
    i.else_case()=code_blockt();

  if(has_else)
  {
    for(++target; target!=before_else; ++target)
      target=convert_instruction(target, before_else, to_code(i.then_case()));

    convert_labels(before_else, to_code(i.then_case()));

    for(++target; target!=end_if; ++target)
      target=convert_instruction(target, end_if, to_code(i.else_case()));
  }
  else
    for(++target; target!=end_if; ++target)
      target=convert_instruction(target, end_if, to_code(i.then_case()));

  dest.move_to_operands(i);
  return --target;
}

/*******************************************************************\

Function: goto_program2codet::convert_goto_break_continue

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_break_continue(
    goto_programt::const_targett target,
    codet &dest)
{
  assert(!loop_last_stack.empty());
  const cfg_dominatorst &dominators=loops.get_dominator_info();

  // goto 1
  // 1: ...
  goto_programt::const_targett next=target;
  for(++next;
      next!=goto_program.instructions.end();
      ++next)
  {
    cfg_dominatorst::cfgt::entry_mapt::const_iterator i_entry=
      dominators.cfg.entry_map.find(next);
    assert(i_entry!=dominators.cfg.entry_map.end());
    const cfg_dominatorst::cfgt::nodet &n=
      dominators.cfg[i_entry->second];

    if(!n.dominators.empty())
      break;
  }

  if(target->get_target()==next)
  {
    dest.copy_to_operands(code_skipt());
    return target;
  }

  goto_programt::const_targett loop_end=loop_last_stack.back().first;

  if(target->get_target()==loop_end &&
     loop_last_stack.back().second)
  {
    code_continuet cont;

    if(!target->guard.is_true())
    {
      code_ifthenelset i;
      i.cond()=target->guard;
      simplify(i.cond(), ns);
      i.then_case().swap(cont);

      dest.move_to_operands(i);
    }
    else
      dest.move_to_operands(cont);

    return target;
  }

  goto_programt::const_targett after_loop=loop_end;
  for(++after_loop;
      after_loop!=goto_program.instructions.end();
      ++after_loop)
  {
    cfg_dominatorst::cfgt::entry_mapt::const_iterator i_entry=
      dominators.cfg.entry_map.find(after_loop);
    assert(i_entry!=dominators.cfg.entry_map.end());
    const cfg_dominatorst::cfgt::nodet &n=
      dominators.cfg[i_entry->second];

    if(!n.dominators.empty())
      break;
  }

  if(target->get_target()==after_loop)
  {
    code_breakt brk;

    code_ifthenelset i;
    i.cond()=target->guard;
    simplify(i.cond(), ns);
    i.then_case().swap(brk);

    if(i.cond().is_true())
      dest.move_to_operands(i.then_case());
    else
      dest.move_to_operands(i);

    return target;
  }

  return convert_goto_goto(target, dest);
}

/*******************************************************************\

Function: goto_program2codet::convert_goto_goto

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_goto(
  goto_programt::const_targett target,
  codet &dest)
{
  // filter out useless goto 1; 1: ...
  goto_programt::const_targett next=target;
  ++next;
  if(target->get_target()==next)
    return target;

  const cfg_dominatorst &dominators=loops.get_dominator_info();
  cfg_dominatorst::cfgt::entry_mapt::const_iterator it_entry=
    dominators.cfg.entry_map.find(target);
  assert(it_entry!=dominators.cfg.entry_map.end());
  const cfg_dominatorst::cfgt::nodet &n=
    dominators.cfg[it_entry->second];

  // skip dead goto L as the label might be skipped if it is dead
  // as well and at the end of a case block
  if(n.dominators.empty())
    return target;

  std::stringstream label;
  // try user-defined labels first
  for(goto_programt::instructiont::labelst::const_iterator
      it=target->get_target()->labels.begin();
      it!=target->get_target()->labels.end();
      ++it)
  {
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_") ||
        has_prefix(id2string(*it), "__CPROVER_DUMP_L"))
      continue;

    label << *it;
    break;
  }

  if(label.str().empty())
    label << "__CPROVER_DUMP_L" << target->get_target()->target_number;

  labels_in_use.insert(label.str());

  code_gotot goto_code(label.str());

  if(!target->guard.is_true())
  {
    code_ifthenelset i;
    i.cond()=target->guard;
    simplify(i.cond(), ns);
    i.then_case().swap(goto_code);

    dest.move_to_operands(i);
  }
  else
    dest.move_to_operands(goto_code);

  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_start_thread

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_start_thread(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  assert(target->is_start_thread());

  goto_programt::const_targett thread_start=target->get_target();
  assert(thread_start->location_number > target->location_number);

  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());

  // first check for old-style code:
  // __CPROVER_DUMP_0: START THREAD 1
  // code in existing thread
  // END THREAD
  // 1: code in new thread
  if(!next->is_goto())
  {
    goto_programt::const_targett this_end=next;
    ++this_end;
    assert(this_end->is_end_thread());
    assert(thread_start->location_number > this_end->location_number);

    codet b=code_blockt();
    convert_instruction(next, this_end, b);

    for(goto_programt::instructiont::labelst::const_iterator
        it=target->labels.begin();
        it!=target->labels.end();
        ++it)
      if(has_prefix(id2string(*it), "__CPROVER_ASYNC_"))
      {
        labels_in_use.insert(*it);

        code_labelt l(*it);
        l.code().swap(b);
        l.add_source_location()=target->source_location;
        b.swap(l);
      }

    assert(b.get_statement()==ID_label);
    dest.move_to_operands(b);
    return this_end;
  }

  // code is supposed to look like this:
  // __CPROVER_ASYNC_0: START THREAD 1
  // GOTO 2
  // 1: code in new thread
  // END THREAD
  // 2: code in existing thread
  /* check the structure and compute the iterators */
  assert(next->is_goto() && next->guard.is_true());
  assert(!next->is_backwards_goto());
  assert(thread_start->location_number < next->get_target()->location_number);
  goto_programt::const_targett after_thread_start=thread_start;
  ++after_thread_start;

  goto_programt::const_targett thread_end=next->get_target();
  --thread_end;
  assert(thread_start->location_number < thread_end->location_number);
  assert(thread_end->is_end_thread());

  assert(upper_bound==goto_program.instructions.end() ||
      thread_end->location_number < upper_bound->location_number);
  /* end structure check */

  // use pthreads if "code in new thread" is a function call to a function with
  // suitable signature
  if(thread_start->is_function_call() &&
      to_code_function_call(to_code(thread_start->code)).arguments().size()==1 &&
      after_thread_start==thread_end)
  {
    const code_function_callt &cf=
      to_code_function_call(to_code(thread_start->code));

    system_headers.insert("pthread.h");

    code_function_callt f;
    // we don't bother setting the type
    f.lhs()=cf.lhs();
    f.function()=symbol_exprt("pthread_create", code_typet());
    exprt n=null_pointer_exprt(pointer_typet(empty_typet()));
    f.arguments().push_back(n);
    f.arguments().push_back(n);
    f.arguments().push_back(cf.function());
    f.arguments().push_back(cf.arguments().front());

    dest.move_to_operands(f);
    return thread_end;
  }

  codet b=code_blockt();
  for( ; thread_start!=thread_end; ++thread_start)
    thread_start=convert_instruction(thread_start, upper_bound, b);

  for(goto_programt::instructiont::labelst::const_iterator
      it=target->labels.begin();
      it!=target->labels.end();
      ++it)
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_"))
    {
      labels_in_use.insert(*it);

      code_labelt l(*it);
      l.code().swap(b);
      l.add_source_location()=target->source_location;
      b.swap(l);
    }

  assert(b.get_statement()==ID_label);
  dest.move_to_operands(b);
  return thread_end;
}

/*******************************************************************\

Function: goto_program2codet::convert_throw

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_throw(
    goto_programt::const_targett target,
    codet &dest)
{
  // this isn't really clear as throw is not supported in expr2cpp either
  assert(false);
  return target;
}

/*******************************************************************\

Function: goto_program2codet::convert_catch

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_catch(
    goto_programt::const_targett target,
    goto_programt::const_targett upper_bound,
    codet &dest)
{
  // this isn't really clear as catch is not supported in expr2cpp either
  assert(false);
  return target;
}

/*******************************************************************\

Function: goto_program2codet::add_local_types

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::add_local_types(const typet &type)
{
  if(type.id()==ID_symbol)
  {
    const typet &full_type=ns.follow(type);

    if(full_type.id()==ID_pointer ||
       full_type.id()==ID_array)
    {
      add_local_types(full_type.subtype());
    }
    else if(full_type.id()==ID_struct ||
            full_type.id()==ID_union)
    {
      const irep_idt &identifier=to_symbol_type(type).get_identifier();
      const symbolt &symbol=ns.lookup(identifier);

      if(symbol.location.get_function().empty() ||
         !type_names_set.insert(identifier).second)
        return;

      const struct_union_typet &struct_union_type=
        to_struct_union_type(full_type);
      const struct_union_typet::componentst &components=
        struct_union_type.components();

      for(struct_union_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          ++it)
        add_local_types(it->type());

      assert(!identifier.empty());
      type_names.push_back(identifier);
    }
  }
  else if(type.id()==ID_c_enum_tag)
  {
    const irep_idt &identifier=to_c_enum_tag_type(type).get_identifier();
    const symbolt &symbol=ns.lookup(identifier);

    if(symbol.location.get_function().empty() ||
       !type_names_set.insert(identifier).second)
      return;

    assert(!identifier.empty());
    type_names.push_back(identifier);
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_array)
  {
    add_local_types(type.subtype());
  }
}

/*******************************************************************\

Function: goto_program2codet::cleanup_code

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_code(
    codet &code,
    const irep_idt parent_stmt)
{
  if(code.get_statement()==ID_decl)
  {
    if(va_list_expr.find(code.op0())!=va_list_expr.end())
      code.op0().type().id(ID_gcc_builtin_va_list);

    Forall_operands(it, code)
      cleanup_expr(*it, true);

    if(code.op0().type().id()==ID_array)
      cleanup_expr(to_array_type(code.op0().type()).size(), true);

    add_local_types(code.op0().type());

    return;
  }
  else if(code.get_statement()==ID_function_call &&
          to_code_function_call(code).function().id()==ID_symbol)
  {
    code_function_callt &call=to_code_function_call(code);
    const symbol_exprt &fn=to_symbol_expr(call.function());
    code_function_callt::argumentst &arguments=call.arguments();

    // don't edit function calls we might have introduced
    const symbolt *s;
    if(!ns.lookup(fn.get_identifier(), s))
    {
      const symbolt &fn_sym=ns.lookup(fn.get_identifier());
      const code_typet &code_type=to_code_type(fn_sym.type);
      const code_typet::parameterst &parameters=code_type.parameters();

      if(parameters.size()==arguments.size())
      {
        code_typet::parameterst::const_iterator it=parameters.begin();
        Forall_expr(it2, arguments)
        {
          if(ns.follow(it2->type()).id()==ID_union)
            it2->type()=it->type();
          ++it;
        }
      }
    }

    while(call.lhs().is_not_nil() &&
          call.lhs().id()==ID_typecast)
      call.lhs()=to_typecast_expr(call.lhs()).op();
  }

  if(code.has_operands())
  {
    exprt::operandst &operands=code.operands();
    Forall_expr(it, operands)
    {
      if(it->id()==ID_code)
        cleanup_code(to_code(*it), code.get_statement());
      else
        cleanup_expr(*it, false);
    }
  }

  const irep_idt &statement=code.get_statement();
  if(statement==ID_label)
  {
    code_labelt &cl=to_code_label(code);
    const irep_idt &label=cl.get_label();

    assert(!label.empty());

    if(labels_in_use.find(label)==labels_in_use.end())
    {
      codet tmp;
      tmp.swap(cl.code());
      code.swap(tmp);
    }
  }
  else if(statement==ID_block)
    cleanup_code_block(code, parent_stmt);
  else if(statement==ID_ifthenelse)
    cleanup_code_ifthenelse(code, parent_stmt);
  else if(statement==ID_dowhile)
  {
    code_dowhilet &do_while=to_code_dowhile(code);

    // turn an empty do {} while(...); into a while(...);
    // to ensure convergence
    if(do_while.body().get_statement()==ID_skip)
      do_while.set_statement(ID_while);
    // do stmt while(false) is just stmt
    else if(do_while.cond().is_false() &&
            do_while.body().get_statement()!=ID_block)
      code=do_while.body();
  }
}

/*******************************************************************\

Function: goto_program2codet::cleanup_code_block

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_code_block(
    codet &code,
    const irep_idt parent_stmt)
{
  assert(code.get_statement()==ID_block);

  exprt::operandst &operands=code.operands();
  for(exprt::operandst::size_type i=0;
      operands.size()>1 && i<operands.size();
     ) // no ++i
  {
    exprt::operandst::iterator it=operands.begin()+i;
    // remove skip
    if(to_code(*it).get_statement()==ID_skip &&
       it->source_location().get_comment().empty())
      operands.erase(it);
    // merge nested blocks, unless there are declarations in the inner block
    else if(to_code(*it).get_statement()==ID_block)
    {
      bool has_decl=false;
      forall_operands(it2, *it)
        if(it2->id()==ID_code && to_code(*it2).get_statement()==ID_decl)
        {
          has_decl=true;
          break;
        }

      if(!has_decl)
      {
        operands.insert(operands.begin()+i+1,
            it->operands().begin(), it->operands().end());
        operands.erase(operands.begin()+i);
        // no ++i
      }
      else
        ++i;
    }
    else
      ++i;
  }

  if(operands.empty() && parent_stmt!=ID_nil)
    code=code_skipt();
  else if(operands.size()==1 &&
          parent_stmt!=ID_nil &&
          to_code(code.op0()).get_statement()!=ID_decl)
  {
    codet tmp;
    tmp.swap(code.op0());
    code.swap(tmp);
  }
}

/*******************************************************************\

Function: goto_program2codet::remove_const

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::remove_const(typet &type)
{
  if(type.get_bool(ID_C_constant))
    type.remove(ID_C_constant);

  if(type.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_type(type).get_identifier();
    if(!const_removed.insert(identifier).second)
      return;

    symbol_tablet::symbolst::iterator it=
      symbol_table.symbols.find(identifier);
    assert(it!=symbol_table.symbols.end());
    assert(it->second.is_type);

    remove_const(it->second.type);
  }
  else if(type.id()==ID_array)
    remove_const(type.subtype());
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    struct_union_typet &sut=to_struct_union_type(type);
    struct_union_typet::componentst &c=sut.components();

    for(struct_union_typet::componentst::iterator
        it=c.begin();
        it!=c.end();
        ++it)
      remove_const(it->type());
  }
}

/*******************************************************************\

Function: has_labels

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static bool has_labels(const codet &code)
{
  if(code.get_statement()==ID_label)
    return true;

  forall_operands(it, code)
    if(it->id()==ID_code && has_labels(to_code(*it)))
      return true;

  return false;
}

/*******************************************************************\

Function: move_label_ifthenelse

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static bool move_label_ifthenelse(
    exprt &expr,
    exprt &label_dest)
{
  if(expr.is_nil() ||
      to_code(expr).get_statement()!=ID_block)
    return false;

  code_blockt &block=to_code_block(to_code(expr));
  if(!block.has_operands() ||
      to_code(block.operands().back()).get_statement()!=ID_label)
    return false;

  code_labelt &label=to_code_label(to_code(block.operands().back()));
  if(label.get_label().empty() ||
      label.code().get_statement()!=ID_skip)
    return false;

  label_dest=label;
  code_skipt s;
  label.swap(s);

  return true;
}

/*******************************************************************\

Function: goto_program2codet::cleanup_code_ifthenelse

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_code_ifthenelse(
  codet &code,
  const irep_idt parent_stmt)
{
  code_ifthenelset &i_t_e=to_code_ifthenelse(code);
  const exprt cond=simplify_expr(i_t_e.cond(), ns);

  // assert(false) expands to if(true) assert(false), simplify again (and also
  // simplify other cases)
  if(cond.is_true() &&
      (i_t_e.else_case().is_nil() || !has_labels(to_code(i_t_e.else_case()))))
  {
    codet tmp;
    tmp.swap(i_t_e.then_case());
    code.swap(tmp);
  }
  else if(cond.is_false() && !has_labels(to_code(i_t_e.then_case())))
  {
    if(i_t_e.else_case().is_nil())
      code=code_skipt();
    else
    {
      codet tmp;
      tmp.swap(i_t_e.else_case());
      code.swap(tmp);
    }
  }
  else
  {
    if(i_t_e.then_case().is_not_nil() &&
       to_code(i_t_e.then_case()).get_statement()==ID_ifthenelse)
    {
      // we re-introduce 1-code blocks with if-then-else to avoid dangling-else
      // ambiguity
      code_blockt b;
      b.move_to_operands(i_t_e.then_case());
      i_t_e.then_case().swap(b);
    }

    if(i_t_e.else_case().is_not_nil() &&
       to_code(i_t_e.then_case()).get_statement()==ID_skip &&
       to_code(i_t_e.else_case()).get_statement()==ID_ifthenelse)
    {
      // we re-introduce 1-code blocks with if-then-else to avoid dangling-else
      // ambiguity
      code_blockt b;
      b.move_to_operands(i_t_e.else_case());
      i_t_e.else_case().swap(b);
    }
  }

  // move labels at end of then or else case out
  if(code.get_statement()==ID_ifthenelse)
  {
    codet then_label=code_skipt(), else_label=code_skipt();

    bool moved=false;
    if(i_t_e.then_case().is_not_nil())
      moved|=move_label_ifthenelse(i_t_e.then_case(), then_label);
    if(i_t_e.else_case().is_not_nil())
      moved|=move_label_ifthenelse(i_t_e.else_case(), else_label);

    if(moved)
    {
      code_blockt b;
      b.move_to_operands(i_t_e);
      b.move_to_operands(then_label);
      b.move_to_operands(else_label);
      code.swap(b);
      cleanup_code(code, parent_stmt);
    }
  }

  // remove empty then/else
  if(code.get_statement()==ID_ifthenelse &&
      to_code(i_t_e.then_case()).get_statement()==ID_skip)
  {
    not_exprt tmp(i_t_e.cond());
    simplify(tmp, ns);
    // simplification might have removed essential type casts
    cleanup_expr(tmp, false);
    i_t_e.cond().swap(tmp);
    i_t_e.then_case().swap(i_t_e.else_case());
  }
  if(code.get_statement()==ID_ifthenelse &&
      i_t_e.else_case().is_not_nil() &&
      to_code(i_t_e.else_case()).get_statement()==ID_skip)
    i_t_e.else_case().make_nil();
  // or even remove the if altogether if the then case is now empty
  if(code.get_statement()==ID_ifthenelse &&
      i_t_e.else_case().is_nil() &&
      (i_t_e.then_case().is_nil() ||
       to_code(i_t_e.then_case()).get_statement()==ID_skip))
    code=code_skipt();
}

/*******************************************************************\

Function: goto_program2codet::cleanup_expr

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_expr(exprt &expr, bool no_typecast)
{
  // we might have to do array -> pointer conversions
  if(no_typecast &&
     (expr.id()==ID_address_of || expr.id()==ID_member))
  {
    Forall_operands(it, expr)
      cleanup_expr(*it, false);
  }
  else if(!no_typecast &&
          (expr.id()==ID_union || expr.id()==ID_struct ||
           expr.id()==ID_array || expr.id()==ID_vector))
  {
    Forall_operands(it, expr)
      cleanup_expr(*it, true);
  }
  else
  {
    Forall_operands(it, expr)
      cleanup_expr(*it, no_typecast);
  }

  if(expr.id()==ID_union ||
     expr.id()==ID_struct)
  {
    if(no_typecast) return;

    assert(expr.type().id()==ID_symbol);

    const typet &t=expr.type();

    add_local_types(t);
    expr=typecast_exprt(expr, t);
  }
  else if(expr.id()==ID_array ||
          expr.id()==ID_vector)
  {
    if(no_typecast ||
       expr.get_bool(ID_C_string_constant))
      return;

    const typet &t=expr.type();

    expr.make_typecast(t);
    add_local_types(t);
  }
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=to_side_effect_expr(expr).get_statement();

    if(statement==ID_nondet)
    {
      // Replace by a function call to nondet_...
      // We first search for a suitable one in the symbol table.
      
      irep_idt id="";
      
      for(symbol_tablet::symbolst::const_iterator
          it=symbol_table.symbols.begin();
          it!=symbol_table.symbols.end();
          it++)
      {
        if(it->second.type.id()!=ID_code) continue;
        if(!has_prefix(id2string(it->second.base_name), "nondet_")) continue;
        const code_typet &code_type=to_code_type(it->second.type);
        if(!type_eq(code_type.return_type(), expr.type(), ns)) continue;
        if(!code_type.parameters().empty()) continue;
        id=it->second.name;
        break;
      }
      
      // none found? make one
      
      if(id=="")
      {
        irep_idt base_name="";
      
        if(expr.type().get(ID_C_c_type)!="")
        {
          irep_idt suffix;
          suffix=expr.type().get(ID_C_c_type);

          if(symbol_table.symbols.find("nondet_"+id2string(suffix))==
             symbol_table.symbols.end())
            base_name="nondet_"+id2string(suffix);
        }
        
        if(base_name=="")
        {
          unsigned count;
          for(count=0;
              symbol_table.symbols.find("nondet_"+i2string(count))!=
              symbol_table.symbols.end();
              count++);
          base_name="nondet_"+i2string(count);
        }
        
        code_typet code_type;
        code_type.return_type()=expr.type();
        
        symbolt symbol;
        symbol.base_name=base_name;
        symbol.name=base_name;
        symbol.type=code_type;
        id=symbol.name;
        
        symbol_table.move(symbol);
      }
      
      const symbolt &symbol=ns.lookup(id);
      
      symbol_exprt symbol_expr(symbol.name, symbol.type);
      symbol_expr.add_source_location()=expr.source_location();
      
      side_effect_exprt call(ID_function_call);
      call.add_source_location()=expr.source_location();
      call.operands().resize(2);
      call.op0()=symbol_expr;
      call.type()=expr.type();
      
      expr.swap(call);
    }
  }
  else if(expr.id()==ID_isnan ||
          expr.id()==ID_sign)
    system_headers.insert("math.h");
  else if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_floatbv)
    {
      const ieee_floatt f(to_constant_expr(expr));
      if(f.is_NaN() || f.is_infinity())
        system_headers.insert("math.h");
    }
    else if(expr.type().id()==ID_pointer)
      add_local_types(expr.type());
    else if(expr.type().id()==ID_bool ||
            expr.type().id()==ID_c_bool)
    {
      expr=from_integer(
        expr.is_true()?1:0,
        signedbv_typet(config.ansi_c.int_width));
      expr.make_typecast(bool_typet());
    }

    const irept &c_sizeof_type=expr.find(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      add_local_types(static_cast<const typet &>(c_sizeof_type));
  }
  else if(expr.id()==ID_typecast)
  {
    if(ns.follow(expr.type()).id()==ID_c_bit_field)
      expr=to_typecast_expr(expr).op();
    else
    {
      add_local_types(expr.type());

      assert(expr.type().id()!=ID_union &&
             expr.type().id()!=ID_struct);
    }
  }
  else if(expr.id()==ID_symbol)
  {
    if(expr.type().id()!=ID_code)
    {
      const irep_idt &identifier=to_symbol_expr(expr).get_identifier();
      const symbolt &symbol=ns.lookup(identifier);

      if(symbol.is_static_lifetime &&
         symbol.type.id()!=ID_code &&
         !symbol.is_extern &&
         !symbol.location.get_function().empty() &&
         local_static_set.insert(identifier).second)
      {
        if(symbol.value.is_not_nil())
        {
          exprt value=symbol.value;
          cleanup_expr(value, true);
        }

        local_static.push_back(identifier);
      }
    }
  }
}

