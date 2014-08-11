/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <set>
#include <map>
#include <list>

#include <util/string2int.h>
#include <util/config.h>
#include <util/hash_cont.h>
#include <util/language.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/replace_symbol.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/suffix.h>
#include <util/base_type.h>
#include <util/type_eq.h>
#include <util/i2string.h>

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <analyses/natural_loops.h>

#include "dump_c.h"

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


class goto_program2codet
{
  typedef std::list<irep_idt> id_listt;
  typedef hash_set_cont<irep_idt,irep_id_hash> id_sett;
  typedef std::map<goto_programt::const_targett, goto_programt::const_targett> loopt;
  typedef hash_map_cont<irep_idt, irep_idt, irep_id_hash> tag_mapt;
  typedef std::multimap<irep_idt, irep_idt> r_tag_mapt;
  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> dead_mapt;
  typedef std::list<std::pair<goto_programt::const_targett, bool> >
    loop_last_stackt;

  struct caset
  {
    const exprt value; // condition upon which this case is taken
    goto_programt::const_targett case_selector; // branching from ...
    goto_programt::const_targett case_start; // ... to
    goto_programt::const_targett case_last; // last instruction of case

    caset(const goto_programt &goto_program,
          const exprt &v,
          goto_programt::const_targett sel,
          goto_programt::const_targett st):
      value(v), case_selector(sel), case_start(st),
      case_last(goto_program.instructions.end())
    {
    }
  };
  typedef std::list<caset> cases_listt;

public:
  goto_program2codet(
      const goto_programt &_goto_program,
      symbol_tablet &_symbol_table,
      const tag_mapt &_tag_map,
      code_blockt &_dest,
      id_listt &_local_static,
      id_listt &_type_names,
      std::set<std::string> &_system_headers):
    goto_program(_goto_program),
    symbol_table(_symbol_table),
    tag_map(_tag_map),
    ns(_symbol_table),
    toplevel_block(_dest),
    local_static(_local_static),
    type_names(_type_names),
    system_headers(_system_headers)
  {
    assert(local_static.empty());

    for(id_listt::const_iterator
        it=type_names.begin();
        it!=type_names.end();
        ++it)
      type_names_set.insert(*it);
  }

  void operator()();

protected:
  const goto_programt &goto_program;
  symbol_tablet &symbol_table;
  const tag_mapt &tag_map;
  const namespacet ns;
  code_blockt &toplevel_block;
  id_listt &local_static;
  id_listt &type_names;
  std::set<std::string> &system_headers;
  exprt va_list_expr;

  natural_loopst loops;
  loopt loop_map;
  id_sett labels_in_use;
  replace_symbolt replace_symbols;
  r_tag_mapt reverse_tag_map;
  id_sett expanded_symbols;
  dead_mapt dead_map;
  loop_last_stackt loop_last_stack;
  id_sett local_static_set;
  id_sett type_names_set;
  id_sett const_removed;

  void build_loop_map();
  void build_dead_map();
  void scan_for_varargs();

  void cleanup_code(codet &code, const irep_idt parent_stmt);

  void cleanup_code_block(
    codet &code,
    const irep_idt parent_stmt);

  void cleanup_code_ifthenelse(
    codet &code,
    const irep_idt parent_stmt);

  void expand_reverse_tag_map(const irep_idt identifier);
  void expand_reverse_tag_map(const typet &type);
  void cleanup_expr(exprt &expr, bool no_typecast);

  void add_local_types(const typet &type);

  void remove_const(typet &type);

  goto_programt::const_targett convert_instruction(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  void convert_labels(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_assign(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_assign_varargs(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
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

  goto_programt::const_targett convert_goto_break_continue(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_goto_goto(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_start_thread(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_throw(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_catch(
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

  replace_symbols.replace(toplevel_block);
  for(id_listt::const_iterator
      it=type_names.begin();
      it!=type_names.end();
      ++it)
  {
    symbolt &symbol=symbol_table.lookup(*it);
    replace_symbols.replace(symbol.type);
  }

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
  va_list_expr.make_nil();

  forall_goto_program_instructions(target, goto_program)
    if(target->is_assign())
    {
      const exprt &r=to_code_assign(target->code).rhs();

      if(r.id()==ID_side_effect &&
         to_side_effect_expr(r).get_statement()==ID_gcc_builtin_va_arg_next)
      {
        assert(r.has_operands());
        va_list_expr=r.op0();
        break;
      }
    }

  if(va_list_expr.is_not_nil())
    system_headers.insert("stdarg.h");
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
    l.location()=target->location;
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
    goto_programt::const_targett upper_bound,
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
  else if(va_list_expr.is_not_nil() &&
          a.lhs()==va_list_expr)
    return convert_assign_varargs(target, upper_bound, dest);
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
              unsigned shl = unsafe_string2unsigned(right.get_string(ID_C_cformat));

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
  const exprt &r=skip_typecast(to_code_assign(target->code).rhs());

  // we don't bother setting the type
  code_function_callt f;
  f.lhs().make_nil();

  if(r.is_zero())
  {
    f.function()=symbol_exprt("va_end", code_typet());
    f.arguments().push_back(va_list_expr);

    dest.move_to_operands(f);
  }
  else if(r.id()==ID_address_of)
  {
    f.function()=symbol_exprt("va_start", code_typet());
    f.arguments().push_back(va_list_expr);
    f.arguments().push_back(to_address_of_expr(r).object());

    dest.move_to_operands(f);
  }
  else if(r.id()==ID_side_effect &&
          to_side_effect_expr(r).get_statement()==ID_gcc_builtin_va_arg_next)
  {
    f.function()=symbol_exprt("va_arg", code_typet());
    f.arguments().push_back(va_list_expr);

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
          skip_typecast(to_dereference_expr(n_r).pointer())==va_list_expr)
       {
         f.lhs()=to_code_assign(next->code).lhs();

         type_of.arguments().push_back(f.lhs());
         f.arguments().push_back(type_of);

         dest.move_to_operands(f);
         return next;
       }
    }

    // assignment not found, still need a proper typeof expression
    assert(r.find("#va_arg_type").is_not_nil());
    const typet &va_arg_type=
      static_cast<typet const&>(r.find("#va_arg_type"));

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
    f.arguments().push_back(va_list_expr);
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
    codet &dest)
{
  code_returnt ret=to_code_return(target->code);

  // catch the specific case where the original code was missing a return
  if(ret.has_return_value() &&
     ret.return_value().id()==ID_side_effect &&
     to_side_effect_expr(ret.return_value()).get_statement()==ID_nondet)
    return target;

  dest.copy_to_operands(ret);

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
       (va_list_expr.is_nil() || a.lhs()!=va_list_expr))
    {
      d.copy_to_operands(a.rhs());

      ++target;
      convert_labels(target, dest);
    }
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
  cfg_dominatorst::node_mapt::const_iterator t_entry=
    dominators.node_map.find(target);
  assert(t_entry!=dominators.node_map.end());
  if(t_entry->second.dominators.empty())
    return convert_goto_if(target, upper_bound, dest);

  // maybe, let's try some more
  code_switcht s;
  s.value()=to_equal_expr(eq_cand).lhs();
  s.body()=code_blockt();

  // find the cases or fall back to convert_goto_if
  goto_programt::const_targett first_target=goto_program.instructions.end();
  goto_programt::const_targett last_target=goto_program.instructions.end();
  std::set<goto_programt::const_targett> unique_targets;

  cases_listt cases;
  goto_programt::const_targett default_target=
    goto_program.instructions.end();

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
           s.value()!=to_equal_expr(*e_it).lhs())
          return convert_goto_if(target, upper_bound, dest);

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
      return convert_goto_if(target, upper_bound, dest);
  }

  // if there are less than 3 targets, we revert to if/else instead; this should
  // help convergence
  if(unique_targets.size()<3)
    return convert_goto_if(target, upper_bound, dest);

  // make sure we don't have some overlap of gotos and switch/case
  if(cases_it==upper_bound ||
     (upper_bound!=goto_program.instructions.end() &&
      upper_bound->location_number < last_target->location_number) ||
     (last_target!=goto_program.instructions.end() &&
      last_target->location_number > default_target->location_number) ||
     target->get_target()==default_target)
    return convert_goto_if(target, upper_bound, dest);

  // backup the top-level block as we might have to backtrack
  code_blockt toplevel_block_bak=toplevel_block;

  // add any instructions that go in the body of the switch before any cases
  goto_programt::const_targett orig_target=target;
  for(target=cases_it; target!=first_target; ++target)
    target=convert_instruction(target, first_target, s.body());

  std::set<unsigned> processed_locations;
  std::map<goto_programt::const_targett, unsigned> targets_done;

  // iterate over all cases to identify block end points
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
      cfg_dominatorst::node_mapt::const_iterator i_entry=
        dominators.node_map.find(case_end);
      assert(i_entry!=dominators.node_map.end());
      const cfg_dominatorst::nodet &n=i_entry->second;

      // ignore dead instructions for the following checks
      if(n.dominators.empty())
        continue;

      // is this instruction dominated by at least one of the cases
      bool some_goto_dom=
        n.dominators.find(it->case_selector)!=n.dominators.end();
      for(cases_listt::const_iterator it2=cases.begin();
          it2!=it && !some_goto_dom;
          ++it2)
        some_goto_dom=
          n.dominators.find(it2->case_selector)!=n.dominators.end();

      // for code that has jumps into one of the cases from outside the
      // switch/case we better use convert_goto_if
      if(n.dominators.find(it->case_start)==n.dominators.end() ||
         !some_goto_dom)
      {
        toplevel_block.swap(toplevel_block_bak);
        return convert_goto_if(orig_target, upper_bound, dest);
      }
      else if(!processed_locations.insert(case_end->location_number).second)
        assert(false);

      it->case_last=case_end;
    }

    targets_done[it->case_start]=1;
  }

  // figure out whether we really had a default target by testing
  // whether all cases eventually jump to the default case
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
        cfg_dominatorst::node_mapt::const_iterator i_entry=
          dominators.node_map.find(next_case);
        assert(i_entry!=dominators.node_map.end());
        const cfg_dominatorst::nodet &n=i_entry->second;

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
        cases.pop_back();
        default_target=goto_program.instructions.end();
      }
    }

    // jumps to default are ok
    if(it->case_last->is_goto() &&
       it->case_last->guard.is_true() &&
       it->case_last->get_target()==default_target)
      continue;

    // fall-through is ok
    if(!it->case_last->is_goto()) continue;

    break;
  }

  // find the last instruction belonging to any of the cases
  goto_programt::const_targett max_target=target;
  for(cases_listt::const_iterator it=cases.begin();
      it!=cases.end();
      ++it)
    if(it->case_last!=goto_program.instructions.end() &&
       it->case_last->location_number > max_target->location_number)
      max_target=it->case_last;

  targets_done.clear();
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
      if(it!=--cases.end())
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
      cfg_dominatorst::node_mapt::const_iterator it_entry=
        dominators.node_map.find(it);
      assert(it_entry!=dominators.node_map.end());
      const cfg_dominatorst::nodet &n=it_entry->second;

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
    cfg_dominatorst::node_mapt::const_iterator i_entry=
      dominators.node_map.find(next);
    assert(i_entry!=dominators.node_map.end());
    const cfg_dominatorst::nodet &n=i_entry->second;

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
    cfg_dominatorst::node_mapt::const_iterator i_entry=
      dominators.node_map.find(after_loop);
    assert(i_entry!=dominators.node_map.end());
    const cfg_dominatorst::nodet &n=i_entry->second;

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
  cfg_dominatorst::node_mapt::const_iterator it_entry=
    dominators.node_map.find(target);
  assert(it_entry!=dominators.node_map.end());
  const cfg_dominatorst::nodet &n=it_entry->second;

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
      l.location()=target->location;
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
    Forall_operands(it, code)
      cleanup_expr(*it, true);

    if(code.op0().type().id()==ID_array)
      cleanup_expr(to_array_type(code.op0().type()).size(), true);

    add_local_types(code.op0().type());

    return;
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

      // nested blocks with declarations become do { } while(false)
      // to ensure the inner block is never lost
      if(has_decl)
      {
        code_dowhilet d;
        d.cond()=false_exprt();
        cleanup_expr(d.cond(), false);
        d.body().swap(*it);

        it->swap(d);

        ++i;
      }
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

  reverse_tag_map.insert(std::make_pair(entry->second, entry->first));

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

void goto_program2codet::cleanup_expr(exprt &expr, bool no_typecast)
{
  expand_reverse_tag_map(expr.type());

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

#if 0
    irep_idt tag=t.get(ID_tag);
    if(tag.empty()) tag=ID_anonymous;

    std::pair<r_tag_mapt::const_iterator, r_tag_mapt::const_iterator>
      reverse_tag_entry=reverse_tag_map.equal_range(tag);

    for( ;
        reverse_tag_entry.first!=reverse_tag_entry.second;
        ++reverse_tag_entry.first)
    {
      symbol_typet new_type(reverse_tag_entry.first->second);
      if(base_type_eq(t, new_type, ns))
      {
        if(expr.id()==ID_union &&
           ns.follow(expr.type()).get_bool(ID_C_transparent_union) !=
           ns.follow(new_type).get_bool(ID_C_transparent_union))
          expr.type()=new_type;

        expr.make_typecast(new_type);
        add_local_types(new_type);

        break;
      }
    }

    if(reverse_tag_entry.first==reverse_tag_entry.second)
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

        if(!type_names_set.insert(t_s.name).second)
          assert(false);
        assert(!t_s.name.empty());
        type_names.push_back(t_s.name);
        if(symbol_table.add(t_s))
          assert(false);
      }

      expr.make_typecast(t);
      add_local_types(t);
    }
#endif
  }
  else if(expr.id()==ID_array ||
          expr.id()==ID_vector)
  {
    if(no_typecast) return;

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

          if(symbol_table.symbols.find("c::nondet_"+id2string(suffix))==
             symbol_table.symbols.end())
            base_name="nondet_"+id2string(suffix);
        }
        
        if(base_name=="")
        {
          unsigned count;
          for(count=0;
              symbol_table.symbols.find("c::nondet_"+i2string(count))!=
              symbol_table.symbols.end();
              count++);
          base_name="nondet_"+i2string(count);
        }
        
        code_typet code_type;
        code_type.return_type()=expr.type();
        
        symbolt symbol;
        symbol.base_name=base_name;
        symbol.name="c::"+id2string(base_name);
        symbol.type=code_type;
        id=symbol.name;
        
        symbol_table.move(symbol);
      }
      
      const symbolt &symbol=ns.lookup(id);
      
      symbol_exprt symbol_expr(symbol.name, symbol.type);
      symbol_expr.location()=expr.location();
      
      side_effect_exprt call(ID_function_call);
      call.location()=expr.location();
      call.operands().resize(2);
      call.op0()=symbol_expr;
      call.type()=expr.type();
      
      expr.swap(call);
    }
  }
  else if(expr.id()==ID_isnan)
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
    else if(expr.type().id()==ID_bool)
    {
      expr=from_integer(
        expr.is_true()?1:0,
        signedbv_typet(config.ansi_c.int_width));
      expr.make_typecast(bool_typet());
    }
    else if((expr.type().id()==ID_unsignedbv ||
             expr.type().id()==ID_signedbv) &&
            expr.type().get(ID_C_c_type)==ID_bool)
    {
      expr=from_integer(
        expr.is_zero()?0:1,
        signedbv_typet(config.ansi_c.int_width));
      expr.make_typecast(bool_typet());
    }

    const irept &c_sizeof_type=expr.find(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      add_local_types(static_cast<const typet &>(c_sizeof_type));
  }
  else if(expr.id()==ID_typecast)
    add_local_types(expr.type());
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
      std::ostream &os_body);
  void convert_compound(
      const typet &type,
      bool recursive,
      std::ostream &os);
  void convert_compound(
      const struct_union_typet &type,
      bool recursive,
      std::ostream &os);

  typedef hash_map_cont<irep_idt, code_declt, irep_id_hash>
          local_static_declst;

  void convert_global_variable(
      const symbolt &symbol,
      std::ostream &os,
      local_static_declst &local_static_decls,
      const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags);

  void convert_function_declaration(
      const symbolt &symbol,
      const bool skip_main,
      std::ostream &os_decl,
      std::ostream &os_body,
      local_static_declst &local_static_decls,
      const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags);

  void insert_local_static_decls(
    code_blockt &b,
    const std::list<irep_idt> &local_static,
    local_static_declst &local_static_decls,
    std::list<irep_idt> &type_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags);

  void insert_local_type_decls(
    code_blockt &b,
    const std::list<irep_idt> &type_decls);

  void cleanup_expr(exprt &expr);
  void cleanup_type(typet &type);
  void cleanup_decl(
    code_declt &decl,
    std::list<irep_idt> &local_static,
    std::list<irep_idt> &local_type_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags);

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
  local_static_declst local_static_decls;
  hash_map_cont<irep_idt, irep_idt, irep_id_hash> original_tags;

  // add copies of struct types when ID_C_transparent_union is only
  // annotated to parameter
  symbol_tablet symbols_transparent;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;

    if(symbol.type.id()!=ID_code) continue;

    code_typet &code_type=to_code_type(symbol.type);
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it2=parameters.begin();
        it2!=parameters.end();
        ++it2)
    {
      typet &type=it2->type();

      if(type.id()==ID_symbol &&
         type.get_bool(ID_C_transparent_union))
      {
        symbolt new_type_sym=
          ns.lookup(to_symbol_type(type).get_identifier());

        new_type_sym.name=id2string(new_type_sym.name)+"$transparent";
        new_type_sym.type.set(ID_C_transparent_union, true);

        // we might have it already, in which case this has no effect
        symbols_transparent.add(new_type_sym);

        to_symbol_type(type).set_identifier(new_type_sym.name);
        type.remove(ID_C_transparent_union);
      }
    }
  }
  forall_symbols(it, symbols_transparent.symbols)
    copied_symbol_table.add(it->second);

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> unique_tagst;
  unique_tagst unique_tags;

  // add tags to anonymous union/struct,
  // and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;

    if((symbol.type.id()==ID_union || symbol.type.id()==ID_struct) &&
       symbol.type.get(ID_tag).empty())
    {
      assert(symbol.is_type);
      symbol.type.set(ID_tag, ID_anonymous);
    }

    const std::string name_str=id2string(it->first);
    if(symbol.is_type && !symbol.type.get(ID_tag).empty())
    {
      irep_idt original_tag=symbol.type.get(ID_tag);
      original_tags[it->first]=original_tag;
      std::string new_tag=id2string(original_tag);

      std::string::size_type tag_pos=new_tag.rfind("tag-");
      if(tag_pos!=std::string::npos)
      {
        new_tag.erase(0, tag_pos+4);
        symbol.type.set(ID_tag, new_tag);
      }

      std::pair<unique_tagst::iterator, bool> unique_entry=
        unique_tags.insert(std::make_pair(symbol.type.get(ID_tag), 0));
      if(!unique_entry.second)
      {
        do
        {
          symbol.type.set(
            ID_tag,
            new_tag+"$"+i2string(unique_entry.first->second));
          ++(unique_entry.first->second);
        }
        while(!unique_tags.insert(std::make_pair(
              symbol.type.get(ID_tag), 0)).second);
      }
    }

    if(!symbols_sorted.insert(name_str).second)
      assert(false);
  }

  // collect all declarations we might need, include local static variables
  bool skip_function_main=false;
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
    {
      if(symbol.location.get_function().empty())
      {
        os << "// " << symbol.name << std::endl;
        os << "// " << symbol.location << std::endl;
        os << type_to_string(symbol.type) << ";" << std::endl;
        os << std::endl;
      }
    }
    else if(symbol.is_static_lifetime && symbol.type.id()!=ID_code)
      convert_global_variable(
          symbol,
          global_var_stream,
          local_static_decls,
          original_tags);
    else if(symbol.type.id()==ID_code)
    {
      goto_functionst::function_mapt::const_iterator func_entry=
        goto_functions.function_map.find(symbol.name);

      if(func_entry!=goto_functions.function_map.end() &&
         func_entry->second.body_available &&
         (symbol.name=="c::main" ||
          (!config.main.empty() && symbol.name==config.main)))
        skip_function_main=true;
    }
  }

  // function declarations and definitions
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.type.id()!=ID_code) continue;

    convert_function_declaration(
      symbol,
      skip_function_main,
      func_decl_stream,
      func_body_stream,
      local_static_decls,
      original_tags);
  }

  // (possibly modified) compound types
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
          compound_body_stream);
  }

  os << std::endl;
  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;
  if(!system_headers.empty()) os << std::endl;

  os << "#ifndef NULL" << std::endl
     << "#define NULL ((void*)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FENCE" << std::endl
     << "#define FENCE(x) ((void)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_EQUAL" << std::endl
     << "#define IEEE_FLOAT_EQUAL(x,y) ((x)==(y))" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_NOTEQUAL" << std::endl
     << "#define IEEE_FLOAT_NOTEQUAL(x,y) ((x)!=(y))" << std::endl
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
    std::ostream &os_body)
{
  if(!symbol.location.get_function().empty())
    return;

  // do compound type body
  if(symbol.type.id()!=ID_incomplete_struct &&
      symbol.type.id()!=ID_incomplete_union)
    convert_compound(
        to_struct_union_type(symbol.type),
        true,
        os_body);
}

/*******************************************************************\

Function: goto2sourcet::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_compound(
  const typet &type,
  bool recursive,
  std::ostream &os)
{
  if(type.id()==ID_symbol)
    convert_compound(ns.follow(type), recursive, os);
  else if(type.id()==ID_array || type.id()==ID_pointer)
  {
    if(!recursive) return;

    convert_compound(type.subtype(), recursive, os);

    // sizeof may contain a type symbol that has to be declared first
    if(type.id()==ID_array)
    {
      find_symbols_sett syms;
      find_type_symbols(to_array_type(type).size(), syms);

      for(find_symbols_sett::const_iterator
          it=syms.begin();
          it!=syms.end();
          ++it)
        convert_compound(symbol_typet(*it), recursive, os);
    }
  }
  else if(type.id()==ID_struct || type.id()==ID_union)
    convert_compound(to_struct_union_type(type), recursive, os);
}

/*******************************************************************\

Function: goto2sourcet::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::convert_compound(
  const struct_union_typet &type,
  bool recursive,
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

    if(recursive && comp_type.id()!=ID_pointer)
      convert_compound(comp_type, recursive, os);

    irep_idt comp_name=comp.get_name();

    struct_body << indent(1) << "// " << comp_name << std::endl;
    struct_body << indent(1);

    // component names such as "main" would collide with other objects in the
    // namespace
    std::string fake_unique_name="NO/SUCH/NS::"+id2string(comp_name);
    std::string s=make_decl(fake_unique_name, comp_type);
    assert(s.find("NO/SUCH/NS")==std::string::npos);

    if(comp.get_is_bit_field() &&
       to_bitvector_type(comp_type).get_width()==0)
    {
      comp_name="";
      s=type_to_string(comp_type);
    }

    if(s.find("__CPROVER_bitvector")==std::string::npos)
    {
      struct_body << s;
      if(comp.get_is_bit_field())
        struct_body << " : " << to_bitvector_type(comp_type).get_width();
    }
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
  if(type.get_bool(ID_C_transparent_union))
    os << " __attribute__ ((__transparent_union__))";
  if(type.get_bool(ID_C_packed))
    os << " __attribute__ ((__packed__))";
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

Function: goto2sourcet::cleanup_decl

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::cleanup_decl(
  code_declt &decl,
  std::list<irep_idt> &local_static,
  std::list<irep_idt> &local_type_decls,
  const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  exprt value=nil_exprt();

  if(decl.operands().size()==2)
  {
    value=decl.op1();
    decl.operands().resize(1);
  }

  goto_programt tmp;
  goto_programt::targett t=tmp.add_instruction(DECL);
  t->code=decl;

  if(value.is_not_nil())
  {
    t=tmp.add_instruction(ASSIGN);
    t->code=code_assignt(decl.op0(), value);
  }

  tmp.add_instruction(END_FUNCTION);

  code_blockt b;
  goto_program2codet p2s(
    tmp,
    copied_symbol_table,
    original_tags,
    b,
    local_static,
    local_type_decls,
    system_headers);
  p2s();

  assert(b.operands().size()==1);
  decl.swap(b.op0());
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
    local_static_declst &local_static_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  // we suppress some declarations
  if(ignore(symbol.name))
    return;

  const irep_idt &func=symbol.location.get_function();
  if((func.empty() || symbol.is_extern || symbol.value.is_not_nil()) &&
      !converted.insert(symbol.name).second)
    return;

  code_declt d(symbol.symbol_expr());

  find_symbols_sett syms;
  if(symbol.value.is_not_nil())
    find_symbols(symbol.value, syms);

  // add a tentative declaration to cater for symbols in the initializer
  // relying on it this symbol
  if((func.empty() || symbol.is_extern) &&
     (symbol.value.is_nil() || !syms.empty()))
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
    os << expr_to_string(d) << std::endl;
  }

  if(!symbol.value.is_nil())
  {
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
        convert_global_variable(sym, os, local_static_decls, original_tags);
    }

    d.copy_to_operands(symbol.value);
  }

  if(!func.empty() && !symbol.is_extern)
    local_static_decls[symbol.name]=d;
  else if(!symbol.value.is_nil())
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;

    std::list<irep_idt> empty_static, empty_types;
    cleanup_decl(d, empty_static, empty_types, original_tags);
    assert(empty_static.empty());
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
    const bool skip_main,
    std::ostream &os_decl,
    std::ostream &os_body,
    local_static_declst &local_static_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  const code_typet &code_type=to_code_type(symbol.type);

  if(ignore(symbol.name))
    return;

  // don't dump artificial main
  if(skip_main && symbol.name==ID_main)
    return;

  // don't dump GCC builtins
  if((symbol.location.get_file()=="gcc_builtin_headers_alpha.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_arm.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_ia32.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_mips.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_power.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_generic.h") &&
     has_prefix(id2string(symbol.name), "c::__builtin_"))
    return;

  if(symbol.name=="c::__builtin_va_start" ||
     symbol.name=="c::__builtin_va_end")
    system_headers.insert("stdarg.h");
  else if(symbol.name!=ID_main &&
          symbol.name!="c::main" &&
          symbol.name!="c::assert")
  {
    os_decl << "// " << symbol.name << std::endl;
    os_decl << "// " << symbol.location << std::endl;
    os_decl << make_decl(symbol.name, code_type) << ";" << std::endl;
  }

  goto_functionst::function_mapt::const_iterator func_entry=
    goto_functions.function_map.find(symbol.name);
  if(func_entry==goto_functions.function_map.end() ||
      !func_entry->second.body_available)
    return;

  code_blockt b;
  std::list<irep_idt> type_decls, local_static;

  goto_program2codet p2s(
      func_entry->second.body,
      copied_symbol_table,
      original_tags,
      b,
      local_static,
      type_decls,
      system_headers);
  p2s();

  insert_local_static_decls(
    b,
    local_static,
    local_static_decls,
    type_decls,
    original_tags);

  convertedt converted_bak(converted);
  insert_local_type_decls(
    b,
    type_decls);
  converted.swap(converted_bak);

  os_body << "// " << symbol.name << std::endl;
  os_body << "// " << symbol.location << std::endl;
  os_body << make_decl(symbol.name, code_type) << std::endl;
  os_body << expr_to_string(b);
  os_body << std::endl << std::endl;
}

/*******************************************************************\

Function: find_block_position_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static bool find_block_position_rec(
  const irep_idt &identifier,
  codet &root,
  code_blockt* &dest,
  exprt::operandst::iterator &before)
{
  if(!root.has_operands())
    return false;

  code_blockt* our_dest=0;

  exprt::operandst &operands=root.operands();
  exprt::operandst::iterator first_found=operands.end();

  Forall_expr(it, operands)
  {
    bool found=false;

    // be aware of the skip-carries-type hack
    if(it->id()==ID_code &&
       to_code(*it).get_statement()!=ID_skip)
      found=find_block_position_rec(
        identifier,
        to_code(*it),
        our_dest,
        before);
    else
    {
      find_symbols_sett syms;
      find_type_and_expr_symbols(*it, syms);

      found=syms.find(identifier)!=syms.end();
    }

    if(!found) continue;

    if(!our_dest)
    {
      // first containing block
      if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=it;
      }

      return true;
    }
    else
    {
      // there is a containing block and this is the first operand
      // that contains identifier
      if(first_found==operands.end())
        first_found=it;
      // we have seen it already - pick the first occurrence in this
      // block
      else if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=first_found;

        return true;
      }
      // we have seen it already - outer block has to deal with this
      else
        return true;
    }
  }

  if(first_found!=operands.end())
  {
    dest=our_dest;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: goto2sourcet::insert_local_static_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::insert_local_static_decls(
  code_blockt &b,
  const std::list<irep_idt> &local_static,
  local_static_declst &local_static_decls,
  std::list<irep_idt> &type_decls,
  const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=local_static.rbegin();
      it!=local_static.rend();
      ++it)
  {
    local_static_declst::const_iterator d_it=
      local_static_decls.find(*it);
    assert(d_it!=local_static_decls.end());

    code_declt d=d_it->second;
    std::list<irep_idt> redundant;
    cleanup_decl(d, redundant, type_decls, original_tags);

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // some use of static variables might be optimised out if it is
    // within an if(false) { ... } block
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, d);
    }
  }
}

/*******************************************************************\

Function: goto2sourcet::insert_local_type_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2sourcet::insert_local_type_decls(
  code_blockt &b,
  const std::list<irep_idt> &type_decls)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=type_decls.rbegin();
      it!=type_decls.rend();
      ++it)
  {
    const typet &type=ns.lookup(*it).type;
    // feed through plain C to expr2c by ending and re-starting
    // a comment block ...
    std::ostringstream os_body;
    os_body << *it << " */\n";
    convert_compound(type, false, os_body);
    os_body << "/*";

    code_skipt skip;
    skip.location().set_comment(os_body.str());
    // another hack to ensure symbols inside types are seen
    skip.type()=type;

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // we might not find it in case a transparent union type cast
    // has been removed by cleanup operations
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, skip);
    }
  }
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
      const bool is_zero_bit_field=
        it->get_is_bit_field() &&
        to_bitvector_type(ns.follow(it->type())).get_width()==0;

      if(!it->get_is_padding() && !is_zero_bit_field)
      {
        type.components().push_back(*it);
        expr.move_to_operands(*o_it);
      }
      ++o_it;
    }
    expr.type().swap(type);
  }
  else if(expr.id()==ID_union &&
          (expr.type().get_bool(ID_C_transparent_union) ||
           ns.follow(expr.type()).get_bool(ID_C_transparent_union)))
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

  assert((type.id()!=ID_union && type.id()!=ID_struct) ||
         !type.get(ID_tag).empty());
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
  else if(expr.id()==ID_side_effect)
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

