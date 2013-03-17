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

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <analyses/natural_loops.h>

#include "dump_c.h"

class goto_program2codet
{
  typedef std::list<irep_idt> type_namest;
  typedef hash_set_cont<irep_idt,irep_id_hash> labelst;
  typedef std::map<goto_programt::const_targett, goto_programt::const_targett> loopt;

public:
  goto_program2codet(
      const goto_programt &_goto_program,
      symbol_tablet &_symbol_table,
      code_blockt &_dest,
      const type_namest &_type_names,
      std::set<std::string> &_system_headers) :
    goto_program(_goto_program),
    symbol_table(_symbol_table),
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
  const namespacet ns;
  code_blockt &toplevel_block;
  const type_namest &type_names;
  std::set<std::string> system_headers;

  loopt loop_map;
  labelst labels_in_use;
  replace_symbolt replace_symbols;

  void build_loop_map();

  void cleanup_code(codet &code, const bool is_top);
  void cleanup_code_block(
      codet &code,
      const bool is_top);
  void cleanup_code_ifthenelse(codet &code);

  goto_programt::const_targett convert_instruction(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

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

  goto_programt::const_targett convert_goto(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
  goto_programt::const_targett convert_goto_while(
      goto_programt::const_targett target,
      goto_programt::const_targett loop_end,
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

  // convert
  forall_goto_program_instructions(target, goto_program)
    target=convert_instruction(
        target,
        goto_program.instructions.end(),
        toplevel_block);

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

  natural_loopst loops;
  loops(goto_program);

  for(natural_loopst::loop_mapt::const_iterator
      l_it=loops.loop_map.begin();
      l_it!=loops.loop_map.end();
      ++l_it)
  {
    assert(!l_it->second.empty());

    goto_programt::const_targett loop_start=l_it->first;
    goto_programt::const_targett loop_end=l_it->first;
    for(natural_loopst::natural_loopt::const_iterator
        it=l_it->second.begin();
        it!=l_it->second.end();
        ++it)
      if((*it)->location_number<loop_start->location_number)
        loop_start=*it;
      else if((*it)->location_number>loop_end->location_number)
        loop_end=*it;
    assert(loop_start==l_it->first);

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
    codet &dest)
{
  assert(target!=goto_program.instructions.end());

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
      /*
         if(!target->location.get_comment().empty())
         inst_stream
         << indent(1)
         << "// "
         << target->location.get_comment();
         */
      dest.copy_to_operands(code_assertt(target->guard));
      return target;

    case ASSUME:
      dest.copy_to_operands(code_assumet(target->guard));
      return target;

    case GOTO:
      return convert_goto(target, upper_bound, dest);

    case START_THREAD:
      return convert_start_thread(target, upper_bound, dest);

    case END_THREAD:
      // inst_stream << indent(1) << "// END_THREAD" << std::endl;
      dest.copy_to_operands(code_assumet(false_exprt()));
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


#if 0
    case OTHER:
      {
        const codet &code=to_code(target->code);
        irep_idt statement=code.get_statement();

        if(statement==ID_expression)
        {
          // expression has no sideeffect
          if(target->is_target())
            inst_stream << indent(1) << "; // OTHER/expression\n";
        }
        else if(has_prefix(id2string(statement), "assign"))
        {
          if(code.op0().id() == "dynamic_size" ||
              code.op0().id() == "valid_object")
          {
            // shall we do something else?
            break;
          }

          inst_stream << indent(1);

          std::string statement = id2string(code.get_statement());
          std::string op_str = statement.substr(std::string("assign").size(), statement.size());

          inst_stream << expr_to_string(target->code.op0()) << " " << op_str << "="
            << expr_to_string(target->code.op1()) << ";" << std::endl;
          break;
        }
        break;
      }
#endif
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
    label << "L" << target->target_number;
    code_labelt l;
    l.set_label(label.str());
    target_label=l.get_label();
    l.code()=code_blockt();
    latest_block->move_to_operands(l);
    latest_block=&to_code_label(
        to_code(latest_block->operands().back())).code();
  }

  for(goto_programt::instructiont::labelst::const_iterator
      it=target->labels.begin();
      it!=target->labels.end();
      ++it)
  {
    if(has_prefix(id2string(*it), "__CPROVER_ASYNC_"))
      continue;
    if(!target_label.empty() && *it==target_label)
      continue;

    // keep all original labels
    labels_in_use.insert(*it);

    code_labelt l;
    l.set_label(*it);
    l.code()=code_blockt();
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
        if(target->code.op0().id() == "dynamic_size" ||
            target->code.op0().id() == "valid_object")
        {
          // shall we do something else?
          break;
        }
        else if(target->code.op0().id()==ID_index)
        {
          const index_exprt &index_expr=to_index_expr(target->code.op0());
          if(index_expr.array().id()==ID_symbol)
            if(supress(index_expr.array().get(ID_identifier)))
              continue;
        }
        else if(target->code.op0().id()==ID_symbol)
        {
          if(supress(target->code.op0().get(ID_identifier)))
            continue;
        }

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
  if(next->is_assign() &&
      next!=upper_bound &&
      &toplevel_block==&dest)
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

  toplevel_block.move_to_operands(d);
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
    return convert_goto_if(target, upper_bound, dest);
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
  assert(loop_end->is_goto());

  if(target==loop_end) // 1: GOTO 1
    return convert_goto_goto(target, dest);

  code_whilet w;
  w.cond()=not_exprt(target->guard);
  simplify(w.cond(), ns);
  w.body()=code_blockt();

  for(++target; target!=loop_end; ++target)
    target=convert_instruction(target, loop_end, w.body());

  convert_labels(loop_end, w.body());

  dest.move_to_operands(w);
  return target;
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

Function: goto_program2codet::convert_goto_goto

Inputs:

Outputs:

Purpose:

\*******************************************************************/

goto_programt::const_targett goto_program2codet::convert_goto_goto(
    goto_programt::const_targett target,
    codet &dest)
{
  std::stringstream label;
  label <<"L" << target->targets.front()->target_number;
  codet goto_code(ID_goto);
  goto_code.set(ID_destination, label.str());

  labels_in_use.insert(label.str());

  if(!target->guard.is_true())
  {
    code_ifthenelset i;
    i.cond()=target->guard;
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

  // code is supposed to look like this:
  // __CPROVER_ASYNC_0: START THREAD 1
  // GOTO 2
  // 1: code in new thread
  // END THREAD
  // 2: code in existing thread
  /* check the structure and compute the iterators */
  goto_programt::const_targett next=target;
  ++next;
  assert(next!=goto_program.instructions.end());
  assert(next->is_goto() && next->guard.is_true());
  assert(next->targets.size()==1 && !next->is_backwards_goto());

  goto_programt::const_targett thread_start=target->targets.front();
  assert(thread_start->location_number > target->location_number);
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
    thread_start=convert_instruction(thread_start, upper_bound, b);

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
  Forall_operands(it, code)
    if(it->id()==ID_code)
      cleanup_code(to_code(*it), false);

  const irep_idt &statement=code.get_statement();
  if(statement==ID_label)
  {
    const irep_idt &label=to_code_label(code).get_label();
    if(labels_in_use.find(label)==labels_in_use.end())
    {
      codet tmp;
      tmp.swap(to_code_label(code).code());
      code.swap(tmp);
    }
  }
  else if(statement==ID_block)
    cleanup_code_block(code, is_top);
  else if(statement==ID_ifthenelse)
    cleanup_code_ifthenelse(code);
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
    if(to_code(*it).get_statement()==ID_skip)
      operands.erase(it);
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
      (code.operands().size()==2 || !has_labels(to_code(i_t_e.else_case()))))
  {
    codet tmp;
    tmp.swap(i_t_e.then_case());
    code.swap(tmp);
  }
  else if(i_t_e.cond().is_false() && !has_labels(to_code(i_t_e.then_case())))
  {
    if(code.operands().size()==2)
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

  std::ostream& print_function_declaration(
    const irep_idt& identifier,
    const code_typet &type,
    const unsigned ptr_level,
    std::ostream &os);

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
      const std::list<irep_idt> &local_type_decls,
      const code_blockt &local_static_decls);

  void cleanup_expr(exprt &expr);
  typedef hash_map_cont<typet, unsigned, irep_hash> anon_mapt;
  anon_mapt anon_renaming;
  irep_idt get_anon_name(const typet& type);
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

  std::map<typet, irep_idt> typedef_map;
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

  // replace all #anon and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    cleanup_type(it->second.type);
    if(!symbols_sorted.insert(id2string(it->first)).second)
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
          local_static_decls[symbol.base_name]);
  }

  os << std::endl;
  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;
  os << "#ifndef TRUE" << std::endl
     << "#define TRUE 1" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FALSE" << std::endl
     << "#define FALSE 0" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef NULL" << std::endl
     << "#define NULL ((void*)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FENCE" << std::endl
     << "#define FENCE(x) ((void)0)" << std::endl
     << "#endif" << std::endl;
  os << std::endl;

#if 0
  os << typedef_stream.str();
  os << std::endl;
  typedef_stream.clear();
#endif

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

#if 0
  if(config.main!="c::main" && config.main!="")
    os << "int main(int argc, const char *argv[])" << std::endl
       << "{" << std::endl
       << indent(1) << config.main << "();" << std::endl
       << indent(1) << "return 0;" << std::endl
       << "}" << std::endl;
#endif
}

/*******************************************************************\

Function: goto2sourcet::print_function_declaration

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::ostream& goto2sourcet::print_function_declaration(
    const irep_idt& identifier,
    const code_typet &type,
    const unsigned ptr_level,
    std::ostream &os)
{
  std::string rett=type_to_string(type.return_type());
  if(type.return_type().id()==ID_pointer &&
      type.return_type().subtype().id()==ID_code)
  {
    static unsigned func_ptr_cnt=0;
    std::stringstream typedef_str;
    typedef_str << "typedef_func_ptr$" << func_ptr_cnt++;
    std::string::size_type name_pos=rett.find("(*)(");
    rett.insert(name_pos+2, typedef_str.str());

    os << "typedef " << rett << ";" << std::endl;
    rett=typedef_str.str();
  }
  os << rett << " ";

  std::string short_name=id2string(identifier);
  std::string::size_type pos=short_name.rfind("::");
  if(pos!=std::string::npos)
    short_name.erase(0, pos+2);
  if(ptr_level>0)
    os << "(" << std::string(ptr_level, '*') << short_name << ")";
  else
    os << short_name;

  os << "(";
  for(code_typet::argumentst::const_iterator
      it=type.arguments().begin();
      it!=type.arguments().end();
      ++it)
  {
    if(it!=type.arguments().begin())
      os << ", ";

    const code_typet::argumentt &arg=*it;
    const symbolt *arg_symb=0;
    ns.lookup(arg.get_identifier(), arg_symb);

    const typet * t_p=&(arg.type());
    unsigned n_ptr=0;
    while(t_p->id()==ID_pointer)
    {
      ++n_ptr;
      t_p=&(t_p->subtype());
    }

    if(t_p->id()==ID_code && n_ptr>0)
    {
      print_function_declaration(
          arg_symb ? arg_symb->base_name : "",
          to_code_type(*t_p),
          n_ptr,
          os);
    }
    else
    {
      if(arg_symb)
      {
        symbol_exprt s(arg_symb->name, arg.type());
        if(has_prefix(id2string(arg_symb->base_name), "#anon"))
        {
          std::string new_name=id2string(arg_symb->name);
          std::string::size_type pos=new_name.find("#anon");
          assert(pos!=std::string::npos);
          new_name[pos]='$';
          s.set_identifier(new_name);
        }

        std::string d_str=expr_to_string(code_declt(s));
        assert(!d_str.empty());
        os << d_str.substr(0, d_str.size()-1);
      }
      else
      {
        os << type_to_string(arg.type());
      }
    }
  }
  if(type.has_ellipsis() && !type.arguments().empty())
    os << ", ...";
  os << ")";

  return os;
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
  if(!symbol.type.location().get_function().empty())
  {
    local_type_decls[symbol.type.location().get_function()].push_back(symbol.name);
    return;
  }

  // do compound type body
  if(symbol.type.id()!=ID_incomplete_struct &&
      symbol.type.id()!=ID_incomplete_union)
    convert_compound_rec(
        to_struct_union_type(symbol.type),
        os_body);

  os_decl << "// " << symbol.name << std::endl;
  os_decl << "// " << symbol.type.location() << std::endl;
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

    base_decls << renamed_base_id.as_string() +
      (parent_it+1==bases.get_sub().end()?"":", ");
      */
  }

  /*
  // for the constructor
  string constructor_args;
  string constructor_body;

  std::string component_name =  renaming[compo.get(ID_name)].as_string();
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
    const struct_typet::componentt& comp=*it;
    typet comp_type=ns.follow(comp.type());

    if(comp_type.id()==ID_code ||
        comp.get_bool(ID_from_base) ||
        comp.get_is_padding())
      continue;

    convert_compound_rec(comp_type, os);

    const irep_idt &comp_name=comp.get_name();
    struct_body << indent(1) << "// " << comp_name << std::endl;
    struct_body << indent(1);

    const typet * t_p=&comp_type;
    unsigned n_ptr=0;
    while(t_p->id()==ID_pointer)
    {
      ++n_ptr;
      t_p=&(t_p->subtype());
    }

    if(t_p->id()==ID_code && n_ptr>0)
      print_function_declaration(
          comp_name,
          to_code_type(*t_p),
          n_ptr,
          struct_body) << ";";
    else
    {
      symbol_exprt sym(comp_name, comp_type);
      code_declt d(sym);
      std::string s=expr_to_string(d);
      if(s.find("__CPROVER_bitvector")==std::string::npos)
        struct_body << s;
      else if(comp_type.id()==ID_signedbv)
      {
        const signedbv_typet &t=to_signedbv_type(comp_type);
        if(t.get_width()<=config.ansi_c.long_long_int_width)
          struct_body << "long long int " << expr_to_string(sym)
            << " : " << t.get_width() << ";";
        else
          assert(false);
      }
      else if(comp_type.id()==ID_unsignedbv)
      {
        const unsignedbv_typet &t=to_unsignedbv_type(comp_type);
        if(t.get_width()<=config.ansi_c.long_long_int_width)
          struct_body << "unsigned long long " << expr_to_string(sym)
            << " : " << t.get_width() << ";";
        else
          assert(false);
      }
      else
        assert(false);
    }
    struct_body << std::endl;
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

  if(symbol.location.get_function().empty() &&
      !converted.insert(symbol.name).second)
    return;

  code_declt d(symbol.symbol_expr());
  if(!symbol.value.is_nil())
  {
    d.copy_to_operands(symbol.value);

    find_symbols_sett syms;
    find_symbols(symbol.value, syms);
    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
    {
      const symbolt &sym=ns.lookup(*it);
      if(!sym.is_type && sym.is_static_lifetime && sym.type.id()!=ID_code)
        convert_global_variable(sym, os, local_static_decls);
    }
  }

  if(!symbol.location.get_function().empty())
    local_static_decls[symbol.location.get_function()].move_to_operands(d);
  else
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
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
    const std::list<irep_idt> &local_type_decls,
    const code_blockt &local_static_decls)
{
  const code_typet &code_type=to_code_type(symbol.type);

  if(symbol.name!="main" &&
      symbol.name!="c::main" &&
      symbol.name!="c::__CPROVER_initialize" &&
      symbol.name!="c::assert" &&
      symbol.name!="c::__assert_rtn" &&
      symbol.name!="c::__CPROVER_assert" &&
      symbol.name!="c::__CPROVER_assume")
  {
    os_decl << "// " << symbol.name << std::endl;
    os_decl << "// " << symbol.location << std::endl;

    print_function_declaration(
        symbol.name,
        code_type,
        0,
        os_decl) << ";" << std::endl;
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

  // don't dump __CPROVER_initialize
  if(symbol.name=="c::__CPROVER_initialize")
    return;

  code_blockt b(local_static_decls);
  goto_program2codet p2s(
      func_entry->second.body,
      copied_symbol_table,
      b,
      local_type_decls,
      system_headers);
  p2s();

  os_body << "// " << symbol.name << std::endl;
  os_body << "// " << symbol.location << std::endl;
  print_function_declaration(
      symbol.name,
      code_type,
      0,
      os_body) << std::endl;
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
    assert(expr.operands().size()==1);
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
  }

  /* this is extremly slow
  else if(expr.id()==ID_constant &&
      expr.find(ID_C_c_sizeof_type).is_not_nil())
    expr.remove(ID_C_c_sizeof_type);*/
}

/*******************************************************************\

Function: goto2sourcet::get_anon_name

Inputs:

Outputs:

Purpose:

\*******************************************************************/

irep_idt goto2sourcet::get_anon_name(const typet& type)
{
  anon_mapt::const_iterator entry=
    anon_renaming.find(type);
  if(entry==anon_renaming.end())
    entry=anon_renaming.insert(
        std::make_pair(
          type,
          anon_renaming.size())).first;

  std::stringstream new_name;
  new_name << "anon$" << entry->second;
  return new_name.str();
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
    tmp.set(ID_tag, get_anon_name(type));
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

