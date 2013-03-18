/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <set>
#include <map>
#include <list>

#include <config.h>
#include <hash_cont.h>
#include <language.h>
#include <std_expr.h>
#include <std_code.h>
#include <std_types.h>
#include <prefix.h>
#include <simplify_expr.h>
#include <replace_symbol.h>
#include <find_symbols.h>
#include <arith_tools.h>
#include <suffix.h>
#include <base_type.h>

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <analyses/natural_loops.h>

#include "dump_c.h"

class goto_program2codet
{
  typedef std::list<irep_idt> type_namest;
  typedef hash_set_cont<irep_idt,irep_id_hash> id_sett;
  typedef std::map<goto_programt::const_targett, goto_programt::const_targett> loopt;
  typedef hash_map_cont<irep_idt, irep_idt, irep_id_hash> tag_mapt;

public:
  goto_program2codet(
      const goto_programt &_goto_program,
      symbol_tablet &_symbol_table,
      const tag_mapt &_tag_map,
      code_blockt &_dest,
      type_namest &_type_names,
      std::set<std::string> &_system_headers) :
    goto_program(_goto_program),
    symbol_table(_symbol_table),
    tag_map(_tag_map),
    ns(_symbol_table),
    toplevel_block(_dest),
    type_names(_type_names),
    system_headers(_system_headers)
  {
  }

  void operator()();

protected:
  const goto_programt &goto_program;
  symbol_tablet &symbol_table;
  const tag_mapt &tag_map;
  const namespacet ns;
  code_blockt &toplevel_block;
  type_namest &type_names;
  std::set<std::string> system_headers;

  natural_loopst loops;
  loopt loop_map;
  id_sett labels_in_use;
  replace_symbolt replace_symbols;
  tag_mapt reverse_tag_map;
  id_sett expanded_symbols;


  void build_loop_map();

  void cleanup_code(codet &code, const bool is_top);
  void cleanup_code_block(
      codet &code,
      const bool is_top);
  void cleanup_code_ifthenelse(codet &code);

  void expand_reverse_tag_map(const irep_idt identifier);
  void expand_reverse_tag_map(const typet &type);
  void cleanup_expr(exprt &expr);

  goto_programt::const_targett convert_instruction(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest,
      bool include_dead_code);

  void convert_labels(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_assign(
      goto_programt::const_targett target,
      codet &dest);
  void convert_assign_rec(
      const code_assignt &assign,
      codet &dest);

  goto_programt::const_targett convert_return(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_decl(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_do_while(
      goto_programt::const_targett target,
      goto_programt::const_targett loop_end,
      codet &dest);

  goto_programt::const_targett convert_goto(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
  goto_programt::const_targett convert_goto_while(
      goto_programt::const_targett target,
      goto_programt::const_targett loop_end,
      codet &dest);
  goto_programt::const_targett convert_goto_switch(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
  goto_programt::const_targett convert_goto_if(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
  goto_programt::const_targett convert_goto_goto(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_start_thread(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
};

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

  // start with a fresh reverse tag map
  reverse_tag_map.clear();
  expanded_symbols.clear();

  // convert
  forall_goto_program_instructions(target, goto_program)
    target=convert_instruction(
        target,
        goto_program.instructions.end(),
        toplevel_block,
        false);

  replace_symbols.replace(toplevel_block);
  for(type_namest::const_iterator
      it=type_names.begin();
      it!=type_names.end();
      ++it)
  {
    symbolt &symbol=symbol_table.lookup(*it);
    replace_symbols.replace(symbol.type);
  }

  cleanup_code(toplevel_block, true);
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
        assert((*it)->targets.size()==1);
        if((*it)->targets.front()==loop_start &&
            (*it)->location_number>loop_end->location_number)
          loop_end=*it;
      }

    if(!loop_map.insert(std::make_pair(loop_start, loop_end)).second)
      assert(false);
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
    codet &dest,
    bool include_dead_code)
{
  assert(target!=goto_program.instructions.end());

  if(!include_dead_code)
  {
    const cfg_dominatorst &dominators=loops.get_dominator_info();
    cfg_dominatorst::node_mapt::const_iterator i_entry=
      dominators.node_map.find(target);
    assert(i_entry!=dominators.node_map.end());
    const cfg_dominatorst::nodet &n=i_entry->second;
    if(n.dominators.find(target)==n.dominators.end())
      return target;
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
      dest.copy_to_operands(code_skipt());
      return target;

    case FUNCTION_CALL:
    case OTHER:
      dest.copy_to_operands(target->code);
      return target;

    case ASSIGN:
      return convert_assign(target, dest);

    case RETURN:
      return convert_return(target, dest);

    case DECL:
      return convert_decl(target, upper_bound, dest);

    case ASSERT:
      system_headers.insert("assert.h");
      dest.copy_to_operands(code_assertt(target->guard));
      dest.operands().back().location().set_comment(
          target->location.get_comment());
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
      dest.operands().back().location().set_comment("END_THREAD");
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

    case DEAD:
    case THROW:
    case CATCH:
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
    code_labelt l;
    l.set_label(label.str());
    target_label=l.get_label();
    l.code()=code_blockt();
    l.location()=target->location;
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

    code_labelt l;
    l.set_label(*it);
    l.code()=code_blockt();
    l.location()=target->location;
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
    codet &dest)
{
  const code_assignt &a=to_code_assign(target->code);

  if(a.lhs().id()==ID_symbol &&
      id2string(to_symbol_expr(a.lhs()).get_identifier()).
      rfind("#array_size")!=std::string::npos)
  {
    replace_symbols.insert(
        to_symbol_expr(a.lhs()).get_identifier(),
        a.rhs());

    dest.copy_to_operands(code_skipt());
  }
  else
    convert_assign_rec(a, dest);

  return target;
#if 0
    case ASSIGN:
      {
        const codet &assign = target->code;
        const exprt &lhs = assign.op0();
        const exprt &rhs = assign.op1();

        //  assignment of the form `a =  (mask & a) |  ((typecast)b) << right' ?
        if(lhs.type().id() == ID_unsignedbv &&
            rhs.id() == ID_bitor &&
            rhs.operands().size() == 2 &&
            rhs.op0().id() == ID_bitand &&
            rhs.op0().operands().size() == 2 &&
            rhs.op1().id() == ID_shl &&
            rhs.op1().operands().size() == 2)
        {
          const exprt& mask = rhs.op0().op0();
          const exprt& a = rhs.op0().op1();
          exprt b = rhs.op1().op0();
          const exprt& right = rhs.op1().op1();

          if(mask.id() == ID_constant && a == lhs && right.id() == ID_constant)
          {
            const std::string& mask_value = mask.get_string(ID_value);

            unsigned l = 0;
            for(; l <  mask_value.size() ; l++)
              if(mask_value[l] == '0')
                break;

            unsigned r = l;
            for(; r <  mask_value.size() ; r++)
              if(mask_value[r] == '1')
                break;


            unsigned trail = r;
            for(; trail <  mask_value.size();trail++)
              if(mask_value[trail] == '0')
                break;

            // because of endidaness...
            l = mask_value.size() - 1 - l;
            r = mask_value.size() - r;

            if(trail == mask_value.size())
            {
              unsigned shl = atoi(right.get(ID_C_cformat).c_str());

              if(r == shl)
              {
                unsigned width = l-r+1;

                if(width == 1 &&
                    b.id() == ID_typecast &&
                    b.op0().type().id() == ID_bool)
                {
                  inst_stream << indent(1) << expr_to_string(a) <<
                    ".set_bit(" << shl <<"," <<
                    expr_to_string(b.op0()) << ");\n" ;
                  break;
                }

                typet new_type(ID_unsignedbv);
                new_type.set(ID_width, width);

                if(b.type() != new_type)
                {
                  if(b.id() == ID_typecast)
                    b.type() = new_type;
                  else
                    b.make_typecast(new_type);
                }

                inst_stream << indent(1) <<
                  expr_to_string(a) <<
                  ".set_range<" << width  <<  ", " << r <<
                  ">( " <<  expr_to_string(b) << ");\n" ;
                break;
              }
            }
          }
        }
      }
#endif
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
  if(assign.rhs().id()==ID_struct)
  {
    const struct_typet &type=
      to_struct_type(ns.follow(assign.rhs().type()));

    const struct_union_typet::componentst &components=
      type.components();

    assert(components.size()==assign.rhs().operands().size());
    exprt::operandst::const_iterator o_it=assign.rhs().operands().begin();
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        ++it)
    {
      if(!it->get_is_padding())
      {
        member_exprt member(assign.lhs(), it->get_name(), it->type());
        convert_assign_rec(code_assignt(member, *o_it), dest);
      }
      ++o_it;
    }
  }
  else if(assign.rhs().id()==ID_array)
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
    codet &dest)
{
  const code_returnt &ret=to_code_return(target->code);

  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());

  // catch the specific case where the original code was missing a return
  // statement to avoid NONDET() in output
  if(ret.has_return_value() &&
      ret.return_value().id()==ID_sideeffect &&
      to_sideeffect_expr(ret.return_value()).get_statement()==ID_nondet &&
      next->is_end_function())
  {
    if(target->is_target())
      dest.copy_to_operands(code_skipt());
  }
  else
    dest.copy_to_operands(target->code);

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

  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());

  // move back initialising assignments into the decl, unless crossing the
  // current boundary
  if(next!=upper_bound &&
      &toplevel_block==&dest &&
      !next->is_target() &&
      next->is_assign())
  {
    const code_assignt &a=to_code_assign(next->code);
    if(a.lhs()==d.symbol())
    {
      d.copy_to_operands(a.rhs());
      ++target;
      convert_labels(target, dest);
    }
  }
  // if we have a constant but can't initialize them right away, we need to
  // remove the const marker
  else if(d.symbol().type().get_bool(ID_C_constant))
    d.symbol().type().remove(ID_C_constant);
  else if(d.symbol().type().id()==ID_array)
  {
    for(typet * t=&(d.symbol().type());
        t->id()==ID_array;
        t=&(t->subtype()))
      if(t->subtype().id()!=ID_array &&
          t->subtype().get_bool(ID_C_constant))
        t->subtype().remove(ID_C_constant);
  }

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

  for( ; target!=loop_end; ++target)
    target=convert_instruction(target, loop_end, d.body(), false);

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
  if(target->targets.front()==after_loop)
  {
    w.cond()=not_exprt(target->guard);
    simplify(w.cond(), ns);
  }
  else
  {
    w.cond().make_true();
    convert_goto_goto(target, w.body());
  }

  for(++target; target!=loop_end; ++target)
    target=convert_instruction(target, loop_end, w.body(), false);

  convert_labels(loop_end, w.body());
  if(!loop_end->guard.is_true())
  {
    code_ifthenelset i;

    i.cond()=not_exprt(loop_end->guard);
    simplify(i.cond(), ns);
    i.then_case()=code_breakt();

    w.body().move_to_operands(i);
  }

  dest.move_to_operands(w);
  return target;
}

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
  if(target->is_backwards_goto() ||
      target->guard.id()!=ID_equal ||
      !skip_typecast(to_equal_expr(target->guard).rhs()).is_constant())
    return convert_goto_if(target, upper_bound, dest);

  // maybe, let's try some more
  const equal_exprt &e1=to_equal_expr(target->guard);
  code_switcht s;
  s.value()=e1.lhs();
  s.body()=code_blockt();

  // find the cases or fall back to convert_goto_if
  goto_programt::const_targett first_target=goto_program.instructions.end();
  goto_programt::const_targett last_target=goto_program.instructions.end();
  std::set<goto_programt::const_targett> unique_targets;

  typedef std::list<std::pair<exprt, std::pair<
    goto_programt::const_targett,
    goto_programt::const_targett> > > cases_listt;
  cases_listt cases;
  goto_programt::const_targett cases_it=target;
  for( ;
      cases_it!=upper_bound && cases_it!=first_target;
      ++cases_it)
  {
    if(cases_it->is_goto() &&
        !cases_it->is_backwards_goto() &&
        cases_it->guard.is_true())
    {
      assert(cases_it->targets.size()==1);
      goto_programt::const_targett default_target=cases_it->targets.front();

      if(first_target==goto_program.instructions.end() ||
          first_target->location_number > default_target->location_number)
        first_target=default_target;
      if(last_target==goto_program.instructions.end() ||
          last_target->location_number < default_target->location_number)
        last_target=default_target;

      cases.push_back(std::make_pair(nil_exprt(),
            std::make_pair(cases_it, default_target)));
      unique_targets.insert(default_target);

      ++cases_it;
      break;
    }
    else if(cases_it->is_goto() &&
        !cases_it->is_backwards_goto() &&
        cases_it->guard.id()==ID_equal &&
        skip_typecast(to_equal_expr(cases_it->guard).rhs()).is_constant() &&
        s.value()==to_equal_expr(cases_it->guard).lhs())
    {
      assert(cases_it->targets.size()==1);
      cases.push_back(std::make_pair(
            to_equal_expr(cases_it->guard).rhs(),
            std::make_pair(cases_it, cases_it->targets.front())));
      assert(cases.back().first.is_not_nil());

      if(first_target==goto_program.instructions.end() ||
          first_target->location_number > cases.back().second.second->location_number)
        first_target=cases.back().second.second;
      if(last_target==goto_program.instructions.end() ||
          last_target->location_number < cases.back().second.second->location_number)
        last_target=cases.back().second.second;

      unique_targets.insert(cases.back().second.second);
    }
    else
      return convert_goto_if(target, upper_bound, dest);
  }

  // make sure we don't have some overlap of gotos and switch/case
  if(cases_it==upper_bound ||
      (upper_bound!=goto_program.instructions.end() &&
       upper_bound->location_number < last_target->location_number))
    return convert_goto_if(target, upper_bound, dest);

  // if there are less than 3 targets, we revert to if/else instead; this should
  // help convergence
  if(unique_targets.size()<3)
    return convert_goto_if(target, upper_bound, dest);

  // add any instructions that go in the body of the switch before any cases
  goto_programt::const_targett orig_target=target;
  for(target=cases_it; target!=first_target; ++target)
    target=convert_instruction(target, first_target, s.body(), true);

  std::set<unsigned> processed_locations;
  const cfg_dominatorst &dominators=loops.get_dominator_info();
  goto_programt::const_targett max_target=target;
  std::map<goto_programt::const_targett, unsigned> targets_done;

  for(cases_listt::const_iterator it=cases.begin();
      it!=cases.end();
      ++it)
  {
    code_labelt cl;
    code_labelt *clp=&cl;
    if(targets_done.find(it->second.second)!=targets_done.end())
      clp=&to_code_label(
          to_code(s.body().operands()[targets_done[it->second.second]]));
    if(it->first.is_nil())
      clp->set(ID_default, true);
    else
      static_cast<exprt&>(clp->add(ID_case)).copy_to_operands(it->first);
    if(clp!=&cl)
    {
      assert(!it->second.first->is_target());
      continue;
    }

    code_blockt c;
    if(it->second.first!=orig_target)
      convert_labels(it->second.first, c);

    target=it->second.second;
    goto_programt::const_targett case_end=target;
    for( ;
        case_end!=goto_program.instructions.end() &&
        case_end!=upper_bound;
        ++case_end)
    {
      cfg_dominatorst::node_mapt::const_iterator i_entry=
        dominators.node_map.find(case_end);
      assert(i_entry!=dominators.node_map.end());
      const cfg_dominatorst::nodet &n=i_entry->second;

      bool some_goto_dom=
        n.dominators.find(it->second.first)!=n.dominators.end();
      for(cases_listt::const_iterator it2=cases.begin();
          it2!=it && !some_goto_dom;
          ++it2)
        some_goto_dom=n.dominators.find(it2->second.first)!=n.dominators.end();

      // this still kills some legitimate cases; in this case we will drop back
      // to convert_goto_if in the check we do below on processed_locations
      if(n.dominators.find(target)==n.dominators.end() || !some_goto_dom)
        break;
      else if(!processed_locations.insert(case_end->location_number).second)
        assert(false);
    }

    // empty case
    if(case_end==target)
    {
      // only emit the jump out of the switch if it's not the last case
      // this improves convergence
      if(it!=--cases.end())
      {
        goto_programt::instructiont i=*(it->second.first);
        i.guard.make_true();
        goto_programt tmp;
        tmp.insert_before_swap(tmp.insert_before(tmp.instructions.end()), i);
        convert_goto_goto(tmp.instructions.begin(), c);
      }
    }
    else
    {
      for( ; target!=case_end; ++target)
        target=convert_instruction(target, case_end, c, false);
      if((--case_end)->location_number > max_target->location_number)
        max_target=case_end;
    }

    cl.code().swap(c);
    targets_done[it->second.second]=s.body().operands().size();
    s.body().move_to_operands(cl);
  }

  // make sure we didn't miss any non-dead instruction
  for(goto_programt::const_targett it=first_target;
      it!=target;
      ++it)
    if(processed_locations.find(it->location_number)==
        processed_locations.end())
    {
      cfg_dominatorst::node_mapt::const_iterator it_entry=
        dominators.node_map.find(it);
      assert(it_entry!=dominators.node_map.end());
      const cfg_dominatorst::nodet &n=it_entry->second;

      if(!n.dominators.empty())
        return convert_goto_if(orig_target, upper_bound, dest);
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
  goto_programt::const_targett else_case=target->targets.front();
  goto_programt::const_targett before_else=else_case;
  goto_programt::const_targett end_if=target->targets.front();
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
      !before_else->is_backwards_goto() &&
      before_else->guard.is_true();

    if(has_else)
    {
      assert(before_else->targets.size()==1);
      end_if=before_else->targets.front();
    }
  }

  code_ifthenelset i;
  i.then_case()=code_blockt();

  // some nesting of loops and branches we might not be able to deal with
  if(target->is_backwards_goto() ||
      (upper_bound!=goto_program.instructions.end() &&
       upper_bound->location_number < end_if->location_number))
    return convert_goto_goto(target, dest);

  i.cond()=not_exprt(target->guard);
  simplify(i.cond(), ns);

  if(has_else)
    i.else_case()=code_blockt();

  if(has_else)
  {
    for(++target; target!=before_else; ++target)
      target=convert_instruction(target, before_else, to_code(i.then_case()), false);

    convert_labels(before_else, to_code(i.then_case()));

    for(++target; target!=end_if; ++target)
      target=convert_instruction(target, end_if, to_code(i.else_case()), false);
  }
  else
    for(++target; target!=end_if; ++target)
      target=convert_instruction(target, end_if, to_code(i.then_case()), false);

  dest.move_to_operands(i);
  return --target;
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
  if(target->targets.front()==next)
    return target;

  std::stringstream label;
  // try user-defined labels first
  for(goto_programt::instructiont::labelst::const_iterator
      it=target->targets.front()->labels.begin();
      it!=target->targets.front()->labels.end();
      ++it)
  {
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_") ||
        has_prefix(id2string(*it), "__CPROVER_DUMP_L"))
      continue;

    label << *it;
    break;
  }
  if(label.str().empty())
    label << "__CPROVER_DUMP_L" << target->targets.front()->target_number;
  labels_in_use.insert(label.str());

  codet goto_code(ID_goto);
  goto_code.set(ID_destination, label.str());

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
  // we only do one target now
  assert(target->targets.size()==1);

  goto_programt::const_targett thread_start=target->targets.front();
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
    convert_instruction(next, this_end, b, false);

    for(goto_programt::instructiont::labelst::const_iterator
        it=target->labels.begin();
        it!=target->labels.end();
        ++it)
      if(has_prefix(id2string(*it), "__CPROVER_ASYNC_"))
      {
        labels_in_use.insert(*it);

        code_labelt l;
        l.set_label(*it);
        l.code().swap(b);
        l.location()=target->location;
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
  assert(next->targets.size()==1 && !next->is_backwards_goto());
  assert(thread_start->location_number < next->targets.front()->location_number);
  goto_programt::const_targett after_thread_start=thread_start;
  ++after_thread_start;

  goto_programt::const_targett thread_end=next->targets.front();
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
    thread_start=convert_instruction(thread_start, upper_bound, b, false);

  for(goto_programt::instructiont::labelst::const_iterator
      it=target->labels.begin();
      it!=target->labels.end();
      ++it)
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_"))
    {
      labels_in_use.insert(*it);

      code_labelt l;
      l.set_label(*it);
      l.code().swap(b);
      l.location()=target->location;
      b.swap(l);
    }

  assert(b.get_statement()==ID_label);
  dest.move_to_operands(b);
  return thread_end;
}

/*******************************************************************\

Function: goto_program2codet::cleanup_code

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_code(
    codet &code,
    const bool is_top)
{
  if(code.has_operands())
  {
    exprt::operandst &operands=code.operands();
    Forall_expr(it, operands)
    {
      if(it->id()==ID_code)
        cleanup_code(to_code(*it), false);
      else
        cleanup_expr(*it);
    }
  }

  const irep_idt &statement=code.get_statement();
  if(statement==ID_label)
  {
    code_labelt &cl=to_code_label(code);

    const irep_idt &label=cl.get_label();
    assert(!label.empty() ||
        !cl.case_op().empty() ||
        cl.is_default());

    if(!label.empty() &&
      labels_in_use.find(label)==labels_in_use.end())
    {
      codet tmp;
      tmp.swap(cl.code());
      code.swap(tmp);
    }
  }
  else if(statement==ID_block)
    cleanup_code_block(code, is_top);
  else if(statement==ID_ifthenelse)
    cleanup_code_ifthenelse(code);
  else if(statement==ID_dowhile)
  {
    code_dowhilet &do_while=to_code_dowhile(code);

    // turn an empty do {} while(...); into a while(...);
    // to ensure convergence
    if(do_while.body().get_statement()==ID_skip)
      do_while.set_statement(ID_while);
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
    const bool is_top)
{
  assert(code.get_statement()==ID_block);

  exprt::operandst &operands=code.operands();
  for(exprt::operandst::size_type i=0;
      operands.size()>1 && i<operands.size();
     ) // no ++i
  {
    exprt::operandst::iterator it=operands.begin()+i;
    // remove skip
    if(to_code(*it).get_statement()==ID_skip)
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

      if(has_decl)
        ++i;
      else
      {
        operands.insert(operands.begin()+i+1,
            it->operands().begin(), it->operands().end());
        operands.erase(operands.begin()+i);
        // no ++i
      }
    }
    else
      ++i;
  }

  if(operands.empty() && !is_top)
    code=code_skipt();
  else if(operands.size()==1 && !is_top)
  {
    codet tmp;
    tmp.swap(code.op0());
    code.swap(tmp);
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

void goto_program2codet::cleanup_code_ifthenelse(codet &code)
{
  code_ifthenelset &i_t_e=to_code_ifthenelse(code);

  // assert(false) expands to if(true) assert(false), simplify again (and also
  // simplify other cases)
  if(i_t_e.cond().is_true() &&
      (i_t_e.else_case().is_nil() || !has_labels(to_code(i_t_e.else_case()))))
  {
    codet tmp;
    tmp.swap(i_t_e.then_case());
    code.swap(tmp);
  }
  else if(i_t_e.cond().is_false() && !has_labels(to_code(i_t_e.then_case())))
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
  else if(to_code(i_t_e.then_case()).get_statement()==ID_ifthenelse)
  {
    // we re-introduce 1-code blocks with if-then-else to avoid dangling-else
    // ambiguity
    code_blockt b;
    b.move_to_operands(i_t_e.then_case());
    i_t_e.then_case().swap(b);
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
      cleanup_code(code, false);
    }
  }

  // remove empty then/else
  if(code.get_statement()==ID_ifthenelse &&
      to_code(i_t_e.then_case()).get_statement()==ID_skip)
  {
    not_exprt tmp(i_t_e.cond());
    simplify(tmp, ns);
    // simplification might have removed essential type casts
    cleanup_expr(tmp);
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

Function: goto_program2codet::expand_reverse_tag_map

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::expand_reverse_tag_map(const irep_idt identifier)
{
  if(!expanded_symbols.insert(identifier).second)
    return;

  tag_mapt::const_iterator entry=tag_map.find(identifier);
  if(entry==tag_map.end())
    return;

  if(!reverse_tag_map.insert(std::make_pair(
          entry->second, entry->first)).second)
  {
    // TODO - ignored for now, as the linker presently produces several
    // symbols for the same type
    // assert(false);
  }

  const symbolt &symbol=symbol_table.lookup(identifier);
  assert(symbol.is_type);
  expand_reverse_tag_map(symbol.type);
}

/*******************************************************************\

Function: goto_program2codet::expand_reverse_tag_map

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::expand_reverse_tag_map(const typet &type)
{
  if(type.id()==ID_symbol)
    expand_reverse_tag_map(to_symbol_type(type).get_identifier());
  else
  {
    find_symbols_sett syms;
    find_type_symbols(type, syms);

    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
      expand_reverse_tag_map(*it);
  }
}

/*******************************************************************\

Function: goto_program2codet::cleanup_expr

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto_program2codet::cleanup_expr(exprt &expr)
{
  expand_reverse_tag_map(expr.type());

  Forall_operands(it, expr)
    cleanup_expr(*it);

  if(expr.id()==ID_union ||
      expr.id()==ID_struct)
  {
    const typet &t=expr.type();

    const irep_idt tag=t.get(ID_tag);
    tag_mapt::const_iterator reverse_tag_entry=reverse_tag_map.find(tag);

    if(reverse_tag_entry!=reverse_tag_map.end())
    {
      symbol_typet new_type(reverse_tag_entry->second);

      if(expr.id()==ID_union &&
          ns.follow(expr.type()).get_bool(ID_C_transparent_union) !=
          ns.follow(new_type).get_bool(ID_C_transparent_union))
        expr.type()=new_type;

      typecast_exprt tc(expr, new_type);
      expr.swap(tc);
    }
    else
    {
      std::string sym_name=id2string(tag);
      if(!t.location().get_function().empty())
        sym_name=id2string(t.location().get_function())+"::"+sym_name;

      if(t.id()!=ID_symbol &&
          !symbol_table.has_symbol(sym_name))
      {
        symbolt t_s;
        t_s.name=sym_name;
        t_s.base_name=t.get(ID_tag);
        t_s.location=expr.location();
        t_s.type=t;
        t_s.is_type=true;
        t_s.is_macro=false;

        type_names.push_back(t_s.name);
        if(symbol_table.add(t_s))
          assert(false);
      }

      typecast_exprt tc(expr, t);
      expr.swap(tc);
    }
  }
  else if(expr.id()==ID_vector)
  {
    const typet &t=expr.type();

    typecast_exprt tc(expr, t);
    expr.swap(tc);
  }
}



class goto2sourcet
{
public:
  goto2sourcet(
    const goto_functionst &_goto_functions,
    const namespacet &_ns,
    language_factoryt factory):
    goto_functions(_goto_functions),
    copied_symbol_table(_ns.get_symbol_table()),
    ns(copied_symbol_table),
    language(factory())
  {
  }

  virtual ~goto2sourcet()
  {
    delete language;
  }

  void operator()(std::ostream &out);

protected:
  const goto_functionst &goto_functions;
  symbol_tablet copied_symbol_table;
  const namespacet ns;
  languaget *language;

  typedef hash_set_cont<irep_idt, irep_id_hash> convertedt;
  convertedt converted;

  typedef hash_map_cont<typet, unsigned, irep_hash, std::equal_to<irept> > anon_mapt;
  anon_mapt anon_renaming;

  static irep_idt get_type_name(
      const typet& type,
      const std::string &prefix,
      goto2sourcet::anon_mapt &map,
      bool &is_new)
  {
    anon_mapt::const_iterator entry=map.find(type);
    is_new=entry==map.end();
    if(is_new)
      entry=map.insert(std::make_pair(type, map.size())).first;

    std::stringstream new_name;
    new_name << prefix << entry->second;
    return new_name.str();
  }

  std::set<std::string> system_headers;

  std::string type_to_string(const typet &type);
  std::string expr_to_string(const exprt &expr);
  static bool ignore(const irep_idt &identifier);

  static std::string indent(const unsigned n)
  {
    return std::string(2*n, ' ');
  }

  std::string make_decl(
      const irep_idt &identifier,
      const typet &type)
  {
    symbol_exprt sym(identifier, type);
    code_declt d(sym);

    std::string d_str=expr_to_string(d);
    assert(!d_str.empty());
    assert(*d_str.rbegin()==';');

    return d_str.substr(0, d_str.size()-1);
  }

  void convert_compound_declaration(
      const symbolt &symbol,
      std::ostream &os_decl,
      std::ostream &os_body,
      hash_map_cont<irep_idt, std::list<irep_idt>, irep_id_hash> &local_type_decls);
  void convert_compound_rec(
      const typet &type,
      std::ostream &os);
  void convert_compound_rec(
      const struct_union_typet &type,
      std::ostream &os);

  void convert_global_variable(
      const symbolt &symbol,
      std::ostream &os,
      hash_map_cont<irep_idt, code_blockt, irep_id_hash> &local_static_decls);

  void convert_function_declaration(
      const symbolt &symbol,
      std::ostream &os_decl,
      std::ostream &os_body,
      std::list<irep_idt> &local_type_decls,
      const code_blockt &local_static_decls,
      const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags);

  void cleanup_expr(exprt &expr);
  void cleanup_type(typet &type);

#if 0
  std::string implicit_declarations(const exprt &expr);
  
  std::string nondet_suffix(const typet &type);

  irep_idt unique_name(const irep_idt name);

  irep_idt get_global_constant(irep_idt cst, irep_idt type_id)
  {
    irep_idt key = id2string(type_id)+"("+id2string(cst)+")";

    std::map<irep_idt, irep_idt>::const_iterator
      it_find=global_constants.find(key);

    if(it_find != global_constants.end())
      return it_find->second;

    irep_idt new_cst_id = unique_name( "__SCOOT_constant");

    global_constants[key] = new_cst_id;
    global_constant_stream << "const " <<
        id2string(type_id) <<" "<< new_cst_id
        <<"(\"" << id2string(cst) << "\");" << std::endl;

    return new_cst_id;
  }

  std::map<irep_idt, irep_idt> global_constants;
  std::map<irep_idt, irep_idt> global_renaming;
  std::map<irep_idt, irep_idt> local_renaming;

  std::stringstream typedef_stream;          // for types
  std::stringstream global_constant_stream;  // for numerical constants

#endif
};

/*******************************************************************\

Function: operator<<

Inputs:

Outputs:

Purpose:

\*******************************************************************/

inline std::ostream &operator << (std::ostream &out, goto2sourcet &src)
{
  src(out);
  return out;
}

/*******************************************************************\

Function: goto2sourcet::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::operator()(std::ostream &os)
{
  std::stringstream func_decl_stream;
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream func_body_stream;
  hash_map_cont<irep_idt, std::list<irep_idt>, irep_id_hash> local_type_decls;
  hash_map_cont<irep_idt, code_blockt, irep_id_hash> local_static_decls;
  hash_map_cont<irep_idt, irep_idt, irep_id_hash> original_tags;

  // replace all #anon, fix $link in types, and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    irep_idt original_tag=it->second.type.get(ID_tag);
    cleanup_type(it->second.type);

    std::string name_str=id2string(it->first);
    if(it->second.is_type && !it->second.type.get(ID_tag).empty())
    {
      original_tags[it->first]=original_tag;

      std::string::size_type link_pos=name_str.rfind("$link");
      if(link_pos!=std::string::npos)
      {
        std::string new_tag=id2string(it->second.type.get(ID_tag));
        if(new_tag.rfind("$link")==std::string::npos)
        {
          new_tag+=name_str.substr(link_pos);
          it->second.type.set(ID_tag, new_tag);
        }
        else
          assert(has_suffix(name_str, new_tag));
      }
    }

    if(!symbols_sorted.insert(name_str).second)
      assert(false);
  }

  // collect all declarations we might need, include local static variables
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.is_type &&
        (symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_incomplete_struct ||
         symbol.type.id()==ID_union ||
         symbol.type.id()==ID_incomplete_union))
      convert_compound_declaration(
          symbol,
          os,
          compound_body_stream,
          local_type_decls);
    else if(symbol.is_static_lifetime && symbol.type.id()!=ID_code)
      convert_global_variable(
          symbol,
          global_var_stream,
          local_static_decls);
  }

  // function declarations and definitions
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.type.id()==ID_code)
      convert_function_declaration(
          symbol,
          func_decl_stream,
          func_body_stream,
          local_type_decls[symbol.base_name],
          local_static_decls[symbol.base_name],
          original_tags);
  }

  os << std::endl;
  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;
  os << "#ifndef TRUE" << std::endl
     << "#define TRUE (_Bool)1" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FALSE" << std::endl
     << "#define FALSE (_Bool)0" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef NULL" << std::endl
     << "#define NULL ((void*)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FENCE" << std::endl
     << "#define FENCE(x) ((void)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_EQUAL" << std::endl
     << "#define IEEE_FLOAT_EQUAL(x,y) (x==y)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_NOTEQUAL" << std::endl
     << "#define IEEE_FLOAT_NOTEQUAL(x,y) (x!=y)" << std::endl
     << "#endif" << std::endl;
  os << std::endl;

  os << func_decl_stream.str();
  os << std::endl;
  os << compound_body_stream.str();
  os << std::endl;

#if 0
  os << global_constant_stream.str();
  global_constant_stream.clear();
#endif

  os << global_var_stream.str();
  os << std::endl;
  os << func_body_stream.str();
}

/*******************************************************************\

Function: goto2sourcet::convert_compound_declarations

Inputs:

Outputs:

Purpose: declare compound types

\*******************************************************************/

void goto2sourcet::convert_compound_declaration(
    const symbolt &symbol,
    std::ostream &os_decl,
    std::ostream &os_body,
    hash_map_cont<irep_idt, std::list<irep_idt>, irep_id_hash> &local_type_decls)
{
  if(!symbol.location.get_function().empty())
  {
    local_type_decls[symbol.location.get_function()].push_back(symbol.name);
    return;
  }

  // do compound type body
  if(symbol.type.id()!=ID_incomplete_struct &&
      symbol.type.id()!=ID_incomplete_union)
    convert_compound_rec(
        to_struct_union_type(symbol.type),
        os_body);

  os_decl << "// " << symbol.name << std::endl;
  os_decl << "// " << symbol.location << std::endl;
  os_decl << type_to_string(symbol.type) << ";" << std::endl;
  os_decl << std::endl;
}

/*******************************************************************\

Function: goto2sourcet::convert_compound_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_compound_rec(
  const typet &type,
  std::ostream &os)
{
  if(type.id()==ID_symbol)
    convert_compound_rec(ns.follow(type), os);
  else if(type.id()==ID_array || type.id()==ID_pointer)
    convert_compound_rec(type.subtype(), os);
  else if(type.id()==ID_struct || type.id()==ID_union)
    convert_compound_rec(to_struct_union_type(type), os);
}

/*******************************************************************\

Function: goto2sourcet::convert_compound_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_compound_rec(
  const struct_union_typet &type,
  std::ostream &os)
{
  const irep_idt &name=type.get(ID_tag);

  if(!converted.insert(name).second)
    return;

  const irept &bases = type.find(ID_bases);
  std::stringstream base_decls;
  forall_irep(parent_it, bases.get_sub())
  {
    assert(false);
    /*
    assert(parent_it->id() == ID_base);
    assert(parent_it->get(ID_type) == ID_symbol);

    const irep_idt &base_id=
      parent_it->find(ID_type).get(ID_identifier);
    const irep_idt &renamed_base_id=global_renaming[base_id];
    const symbolt &parsymb=ns.lookup(renamed_base_id);

    convert_compound_rec(parsymb.type, os);

    base_decls << id2string(renamed_base_id) +
      (parent_it+1==bases.get_sub().end()?"":", ");
      */
  }

  /*
  // for the constructor
  string constructor_args;
  string constructor_body;

  std::string component_name =  id2string(renaming[compo.get(ID_name)]);
  assert(component_name != "");

  if(it != struct_type.components().begin()) constructor_args += ", ";

  if(compo.type().id() == ID_pointer)
  constructor_args += type_to_string(compo.type()) + component_name;
  else
  constructor_args += "const " + type_to_string(compo.type()) + "& " + component_name;

  constructor_body += indent + indent + "this->"+component_name + " = " + component_name + ";\n";
  */

  std::stringstream struct_body;

  for(struct_union_typet::componentst::const_iterator
      it=type.components().begin();
      it!=type.components().end();
      it++)
  {
    const struct_typet::componentt &comp=*it;
    typet comp_type=ns.follow(comp.type());

    if(comp_type.id()==ID_code ||
       comp.get_bool(ID_from_base) ||
       comp.get_is_padding())
      continue;

    convert_compound_rec(comp_type, os);

    const irep_idt &comp_name=comp.get_name();

    struct_body << indent(1) << "// " << comp_name << std::endl;
    struct_body << indent(1);

    // component names such as "main" would collide with other objects in the
    // namespace
    std::string fake_unique_name="NO/SUCH/NS::"+id2string(comp_name);
    std::string s=make_decl(fake_unique_name, comp_type);
    assert(s.find("NO/SUCH/NS")==std::string::npos);

    if(s.find("__CPROVER_bitvector")==std::string::npos)
      struct_body << s;
    else if(comp_type.id()==ID_signedbv)
    {
      const signedbv_typet &t=to_signedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "long long int " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__signedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else if(comp_type.id()==ID_unsignedbv)
    {
      const unsignedbv_typet &t=to_unsignedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "unsigned long long " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__unsignedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else
      assert(false);

    struct_body << ";" << std::endl;
  }

  os << type_to_string(type);
  if(!base_decls.str().empty())
  {
    assert(language->id()=="cpp");
    os << ": " << base_decls.str();
  }
  os << std::endl;
  os << "{" << std::endl;
  os << struct_body.str();

  /*
     if(!struct_type.components().empty())
     {
     os << indent << name << "(){}\n";
     os << indent << "explicit " << name
     << "(" + constructor_args + ")\n";
     os << indent << "{\n";
     os << constructor_body;
     os << indent << "}\n";
     }
     */

  os << "}";
  if(ns.follow(type).get_bool(ID_C_transparent_union))
    os << " __attribute__ ((__transparent_union__))";
  os << ";";
  os << std::endl;
  os << std::endl;
}

/*******************************************************************\

Function: goto2sourcet::supress

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool goto2sourcet::ignore(const irep_idt &identifier)
{
  return (has_prefix(id2string(identifier), "c::__CPROVER_") ||
     identifier=="c::__func__" ||
     identifier=="c::__FUNCTION__" ||
     identifier=="c::__PRETTY_FUNCTION__" ||
     identifier=="c::argc'" ||
     identifier=="c::argv'" ||
     identifier=="c::envp'" ||
     identifier=="c::envp_size'");
}

/*******************************************************************\

Function: goto2sourcet::convert_global_variables

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_global_variable(
    const symbolt &symbol,
    std::ostream &os,
    hash_map_cont<irep_idt, code_blockt, irep_id_hash> &local_static_decls)
{
  // we suppress some declarations
  if(ignore(symbol.name))
    return;

  if((symbol.location.get_function().empty() || symbol.is_extern) &&
      !converted.insert(symbol.name).second)
    return;

  code_declt d(symbol.symbol_expr());
  // add a tentative declaration to cater for symbols in the initializer
  // relying on it this symbol
  if(symbol.location.get_function().empty() || symbol.is_extern)
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
    if(symbol.is_file_local)
      os << "static ";
    os << expr_to_string(d) << std::endl;
  }

  if(!symbol.value.is_nil())
  {
    d.copy_to_operands(symbol.value);

    find_symbols_sett syms;
    find_symbols(symbol.value, syms);

    std::set<std::string> symbols_sorted;
    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
      if(!symbols_sorted.insert(id2string(*it)).second)
        assert(false);

    for(std::set<std::string>::const_iterator
        it=symbols_sorted.begin();
        it!=symbols_sorted.end();
        ++it)
    {
      const symbolt &sym=ns.lookup(*it);
      if(!sym.is_type && sym.is_static_lifetime && sym.type.id()!=ID_code)
        convert_global_variable(sym, os, local_static_decls);
    }
  }

  if(!symbol.location.get_function().empty() && !symbol.is_extern)
    local_static_decls[symbol.location.get_function()].move_to_operands(d);
  else if(!symbol.value.is_nil())
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
    if(symbol.is_file_local)
      os << "static ";
    os << expr_to_string(d) << std::endl;
  }
}

/*******************************************************************\

Function: goto2sourcet::convert_function_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_function_declaration(
    const symbolt& symbol,
    std::ostream &os_decl,
    std::ostream &os_body,
    std::list<irep_idt> &local_type_decls,
    const code_blockt &local_static_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  const code_typet &code_type=to_code_type(symbol.type);

  if(ignore(symbol.name))
    return;

  if(symbol.name!="main" &&
      symbol.name!="c::main" &&
      symbol.name!="c::assert")
  {
    os_decl << "// " << symbol.name << std::endl;
    os_decl << "// " << symbol.location << std::endl;

    if(symbol.is_file_local)
      os_decl << "static ";
    os_decl << make_decl(symbol.name, code_type) << ";" << std::endl;
  }

  goto_functionst::function_mapt::const_iterator func_entry=
    goto_functions.function_map.find(symbol.name);
  if(func_entry==goto_functions.function_map.end() ||
      !func_entry->second.body_available)
    return;

  // don't dump artificial main
  if(symbol.name=="main" &&
      (config.main=="c::main" || config.main==""))
    return;

  code_blockt b(local_static_decls);
  goto_program2codet p2s(
      func_entry->second.body,
      copied_symbol_table,
      original_tags,
      b,
      local_type_decls,
      system_headers);
  p2s();

  os_body << "// " << symbol.name << std::endl;
  os_body << "// " << symbol.location << std::endl;
  if(symbol.is_file_local)
    os_body << "static ";
  os_body << make_decl(symbol.name, code_type) << std::endl;
  os_body << "{";

  convertedt converted_bak(converted);
  for(std::list<irep_idt>::const_iterator
      it=local_type_decls.begin();
      it!=local_type_decls.end();
      ++it)
  {
    os_body << std::endl;
    convert_compound_rec(ns.lookup(*it).type, os_body);
  }
  converted.swap(converted_bak);

  os_body << expr_to_string(b).substr(1);
  os_body << std::endl << std::endl;
}

/*******************************************************************\

Function: goto2sourcet::cleanup_expr

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::cleanup_expr(exprt &expr)
{
  Forall_operands(it, expr)
    cleanup_expr(*it);

  cleanup_type(expr.type());

  if(expr.id()==ID_struct)
  {
    struct_typet type=
      to_struct_type(ns.follow(expr.type()));

    struct_union_typet::componentst old_components;
    old_components.swap(type.components());

    exprt::operandst old_ops;
    old_ops.swap(expr.operands());

    assert(old_components.size()==old_ops.size());
    exprt::operandst::iterator o_it=old_ops.begin();
    for(struct_union_typet::componentst::const_iterator
        it=old_components.begin();
        it!=old_components.end();
        ++it)
    {
      if(!it->get_is_padding())
      {
        type.components().push_back(*it);
        expr.move_to_operands(*o_it);
      }
      ++o_it;
    }
    expr.type().swap(type);
  }
  else if(expr.id()==ID_union &&
      ns.follow(expr.type()).get_bool(ID_C_transparent_union))
  {
    union_exprt &u=to_union_expr(expr);

    // add a typecast for NULL
    if(u.op().type().id()==ID_pointer &&
        u.op().type().subtype().id()==ID_empty &&
        u.op().is_zero())
    {
      const struct_union_typet::componentt &comp=
        to_union_type(u.type()).get_component(u.get_component_name());
      const typet &u_op_type=comp.type();
      assert(u_op_type.id()==ID_pointer);

      typecast_exprt tc(u.op(), u_op_type);
      expr.swap(tc);
    }
    else
    {
      exprt tmp;
      tmp.swap(u.op());
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_typecast &&
      expr.op0().id()==ID_typecast &&
      base_type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp=expr.op0();
    expr.swap(tmp);
  }
}

/*******************************************************************\

Function: goto2sourcet::cleanup_type

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::cleanup_type(typet &type)
{
  Forall_subtypes(it, type)
    cleanup_type(*it);

  if(type.id()==ID_array)
    cleanup_expr(to_array_type(type).size());

  if(!type.get(ID_tag).empty() &&
      has_prefix(type.get_string(ID_tag), "#anon"))
  {
    typet tmp=type;
    bool b;
    tmp.set(ID_tag, get_type_name(type, "anon$", anon_renaming, b));
    type.swap(tmp);
  }
}

/*******************************************************************\

Function: goto2sourcet::type_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2sourcet::type_to_string(const typet &type)
{
  std::string ret;
  typet t=type;
  cleanup_type(t);
  language->from_type(t, ret, ns);
  return ret;

#if 0
  if(type.id()==ID_bool)
    #if 0
    ret="bool";
    #else
    ret="_Bool";
    #endif
  else if(type.id()==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "int";
    else if(width==config.ansi_c.char_width)
      return "signed char";
    else if(width==config.ansi_c.short_int_width)
      return "short int";
    else if(width==config.ansi_c.long_int_width)
      return "long int";
    else if(width==config.ansi_c.long_long_int_width)
      return "long long int";
    else
      return "__signedbv<"+i2string(width)+">";
  }
  else if(type.id()==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "unsigned int";
    else if(width==config.ansi_c.char_width)
      return "unsigned char";
    else if(width==config.ansi_c.short_int_width)
      return "unsigned short int";
    else if(width==config.ansi_c.long_int_width)
      return "unsigned long int";
    else if(width==config.ansi_c.long_long_int_width)
      return "unsigned long long int";
    else
      return "__unsignedbv<"+i2string(width)+">";
  }
  else if(type.id()==ID_verilogbv)
  {
    return "__verilogbv<"+id2string(type.get(ID_width))+"> ";
  }
#endif
}

/*******************************************************************\

Function: goto2sourcet::expr_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2sourcet::expr_to_string(const exprt &expr)
{
  std::string ret;
  exprt e=expr;
  cleanup_expr(e);
  language->from_expr(e, ret, ns);
  return ret;

#if 0
  else if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv)
    {
      std::string width_str = id2string(expr.type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);

      mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return str;

      #if 0

      if(width <= config.ansi_c.int_width)
      {
        mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
        std::string str = integer2string(cst, 10) ;
        assert(str != "");
        return "__" + id2string(expr.type().id()) + "<" + width_str + "> ( " + str +")";
      }
      else
      {
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return id2string(get_global_constant(id2string(expr.get(ID_value)), type_id));
      }
      #endif
    }

    if(expr.type().id()==ID_bool)
      return expr.is_true()?"1":"0";

    if(expr.type().id()==ID_pointer)
    {
      assert(expr.get(ID_value)==ID_NULL);
      return "0";
    }

    if(expr.type().id()==ID_verilogbv)
    {
      if(expr.type().get(ID_width)=="1")
      {
        irep_idt value = expr.get(ID_value);
        if(value == "0")
          return "LOGIC_0";
        if(value == "1")
          return "LOGIC_1";
        if(value == "z")
          return "LOGIC_Z";
        if(value == "x")
          return "LOGIC_X";
      }
      else
      {
        std::string width_str = id2string(expr.type().get(ID_width));
        mp_integer width = string2integer(width_str,10);
        assert(width != 0);
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return  type_id +"("+ id2string(get_global_constant(expr.get("value"), type_id))+")";
      }
    }

    #if 0
    if(expr.type().id()==ID_c_enum)
    {
      std::string str = "__signedbv<" + id2string(expr.type().get(ID_width)) +
        "> (" + id2string(expr.get(ID_value)) + ")";
      return str;
    }
    #endif

    if(expr.type().id()==ID_symbol)
    {
      typet final_type = ns.follow(expr.type());
      exprt expr2(expr);
      expr2.type() = final_type;
      return expr_to_string(expr2);
    }
  }
  else if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    
    if(expr.type().id()==ID_bool)
    {
      return "("+type_to_string(expr.type())+")("+
             expr_to_string(expr.op0())+")";
    }

    if(expr.type().id() == ID_pointer && 
       expr.op0().type().id() == ID_pointer)
    {
      const typet& subtype = ns.follow(expr.type().subtype());
      const typet& op_subtype = ns.follow(expr.op0().type().subtype());
      if(subtype.id() == ID_struct &&
          op_subtype.id() == ID_struct)
      {
        std::list<irep_idt> wkl;

        wkl.push_back(subtype.get(ID_name));
        std::set<irep_idt> bases;
        while(!wkl.empty())
        {
          irep_idt id = wkl.back();
          wkl.pop_front();
          bases.insert(id);
          const symbolt& symb = ns.lookup(id);
          const struct_typet& struct_type = to_struct_type(symb.type);
          const irept::subt& subs = struct_type.find(ID_bases).get_sub();
          for(unsigned i = 0; i < subs.size(); i++)
            wkl.push_back(subs[i].find(ID_type).get(ID_identifier));
        }

        if(bases.count(op_subtype.get(ID_name)))
        {
          return "static_cast<" + type_to_string(expr.type()) + "> (" +
                 expr_to_string(expr.op0()) + ")";
        }

        bases.clear();
        wkl.clear();
        wkl.push_back(op_subtype.get(ID_name));
        while(!wkl.empty())
        {
          irep_idt id = wkl.back();
          wkl.pop_front();
          bases.insert(id);
          const symbolt& symb = ns.lookup(id);
          const struct_typet& struct_type = to_struct_type(symb.type);
          const irept::subt& subs = struct_type.find(ID_bases).get_sub();
          for(unsigned i = 0; i < subs.size(); i++)
            wkl.push_back(subs[i].find(ID_type).get(ID_identifier));
        }

        //if(bases.count(subtype.get(ID_name)))
        {
          return "static_cast<" + type_to_string(expr.type()) + "> (" +
                 expr_to_string(expr.op0()) + ")";
        }

        std::cerr << "Warning conversion from " << op_subtype.get("name")
                  << " to " << subtype.get(ID_name) << " is not safe!\n";
      }
    }

    return "((" + type_to_string(expr.type()) + ") " +
           expr_to_string(expr.op0()) + ")";
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size() == 1);
    return "(&"+expr_to_string(expr.op0())+")";
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size() == 2);

    if(expr.op1().id()==ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv ||
             expr.op1().type().id() == ID_signedbv);

      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str, 10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)), 2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return "(" +expr_to_string(expr.op0()) + "[" + str + " ] )";
    }

    return "(" +expr_to_string(expr.op0())+
           "[" + expr_to_string(expr.op1())+ "])";
  }
  else if(expr.id() == ID_extractbits)
  {
    assert(expr.operands().size()==3);

    return "__" + id2string(expr.type().id())
           + "<"+ id2string(expr.type().get(ID_width)) + "> ("
           + expr_to_string(expr.op0()) + ", "
           + expr_to_string(expr.op1()) + ", "
           + expr_to_string(expr.op2()) + " )";
  }
  else if(expr.id() == ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return "((" + expr_to_string(expr.op0()) + ")[ "+ str + " ])";
    }

    return "((" + expr_to_string(expr.op0()) + ")[ "
           + expr_to_string(expr.op1()) + " ])";
  }
  else if(expr.id()==ID_sideeffect)
  {
    const irep_idt &statement=to_sideeffect_expr(expr).get_statement();
  
    if(statement==ID_cpp_new)
    {
      assert(expr.type().id()==ID_pointer);
      return "new "+type_to_string(expr.type().subtype())+"()";
    }
    else if(statement==ID_cpp_new_array)
    {
      assert(expr.type().id()==ID_pointer);
      return "(new " + type_to_string(expr.type().subtype()) +
             "[ " + expr_to_string((const exprt &)expr.find(ID_size)) + "])";
    }
    else if(statement==ID_nondet)
    {
      return "nondet_"+nondet_suffix(expr.type())+"()";
    }
  }
  else if(expr.id() == ID_string_constant)
  {
    std::string get_value = expr.get_string(ID_value);
    std::string filtered_value;
    for(unsigned i=0; i < get_value.length(); i++)
    {
      if(get_value[i] == '\n')
        filtered_value += "\\n";
      else if(get_value[i] == '\\')
        filtered_value +="\\\\";
      else if(get_value[i] == '\"')
        filtered_value += "\\\"";
      else
        filtered_value += get_value[i];
      filtered_value += "\\000\\000\\000";  //  convert char to int.
    }
    filtered_value +="\\000\\000\\000";
    return "((__signedbv<8>*)\""+ filtered_value +"\")";
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    return "("+expr_to_string(expr.op0())+
           "? "+expr_to_string(expr.op1())+
           ":"+expr_to_string(expr.op2())+")";
  }
  else if(expr.id() == ID_infinity)
  {
    return "CPROVER_INFINITY";
  }
  else if(expr.id() == ID_concatenation)
  {
    return "__concatenation( "
           + expr_to_string(expr.op0())
           + ", " + expr_to_string(expr.op1())
           + ")";
  }
  else if(expr.id() == ID_with)
  {
    assert(expr.operands().size() == 3);

    if(expr.op0().type().id() == ID_array)
    {
      std::string T = type_to_string(expr.type().subtype());
      std::string W = expr_to_string(
          to_array_type(expr.type()).size());

      std::string src = expr_to_string(expr.op0());
      std::string index = expr_to_string(expr.op1());
      std::string value = expr_to_string(expr.op2());

      std::string ret = "(__array< "+ T + ", " + W  + " >&)";

      if(expr.op0().id() == ID_with)
      {
        // fast version: src[index] = v
        ret += "__with< " + T + ", " + W  + " >" +
               "(" + src + ", " + index + ", " + value + ")";
      }
      else
      {
        // slow version: src is duplicated
        ret += "__const_with< " + T + ", " + W  + ">" +
          "(" + src + ", " + index + ", " + value + ")";
      }
      ret = "(" +ret + ")";
      return ret;
    }
    else
    {
      const typet &t=ns.follow(expr.type());
      assert(t.id() == ID_struct);

      std::string src = expr_to_string(expr.op0());
      std::string value = expr_to_string(expr.op2());

      std::string member =
        id2string(global_renaming[expr.get(ID_component_name)]);

      std::string type =
        id2string(global_renaming[t.get(ID_name)]);

      return "__with("+ src+ ", &" + type + "::" + member + ", " +
        value + ")";
    }
  }
  else if(expr.id() == ID_array_of)
  {
    assert(expr.operands().size() == 1);
    assert(expr.type().id() == ID_array);
    assert(expr.type().subtype() == expr.op0().type());

    std::string T = type_to_string(expr.type().subtype());
    std::string W = expr_to_string(
      to_array_type(expr.type()).size());
    std::string arg = expr_to_string(expr.op0());
    return "__array<" + T + ", " + W + " >("+ arg + ")";
  }
  else if(expr.id() == ID_struct)
  {
    const struct_typet& struct_type = 
      to_struct_type(ns.follow(expr.type()));
    const struct_typet::componentst& components = struct_type.components();
    const exprt::operandst& operands = expr.operands();

    std::string ret=id2string(global_renaming[struct_type.get(ID_name)])+"(";
    
    assert(operands.size() == components.size());
    if( 0 < operands.size())
    {
      assert(operands[0].type() == components[0].type());
      ret += expr_to_string(operands[0]);
    }

    for(unsigned i = 1; i < operands.size(); i++)
    {
      assert(operands[i].type() == components[i].type());
      ret += ", " +expr_to_string(operands[i]);
    }
    ret += ")";
    return ret;
  }
  else if(expr.id() == ID_pointer_object)
  {
    return "POINTER_OBJECT";
  }

  //ps_irep("expr",expr);
  std::cout << expr << std::endl;
  assert(0);
#endif
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  goto2sourcet goto2c(src, ns, new_ansi_c_language);
  out << goto2c;
}

/*******************************************************************\

Function: dump_cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_cpp(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  goto2sourcet goto2cpp(src, ns, new_cpp_language);
  out << goto2cpp;
}

