/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation

#include "mm_io.h"

#include <util/pointer_predicates.h>
#include <util/pointer_offset_size.h>
#include <util/replace_expr.h>

#include "remove_returns.h"

void collect_deref_expr(
  const exprt &src,
  std::set<dereference_exprt> &dest)
{
  src.visit_pre([&dest](const exprt &e) {
    if(e.id() == ID_dereference)
      dest.insert(to_dereference_expr(e));
  });
}

void mm_io(
  const exprt &mm_io_r,
  const exprt &mm_io_w,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  for(goto_programt::instructionst::iterator it=
      goto_function.body.instructions.begin();
      it!=goto_function.body.instructions.end();
      it++)
  {
    std::set<dereference_exprt> deref_expr_w, deref_expr_r;

    if(it->is_assign())
    {
      auto a = it->get_assign();
      collect_deref_expr(a.rhs(), deref_expr_r);

      if(mm_io_r.is_not_nil())
      {
        if(deref_expr_r.size()==1)
        {
          const dereference_exprt &d=*deref_expr_r.begin();
          source_locationt source_location=it->source_location;
          const code_typet &ct=to_code_type(mm_io_r.type());

          irep_idt identifier=to_symbol_expr(mm_io_r).get_identifier();
          auto return_value = return_value_symbol(identifier, ns);
          if_exprt if_expr(integer_address(d.pointer()), return_value, d);
          if(!replace_expr(d, if_expr, a.rhs()))
            it->set_assign(a);

          const typet &pt=ct.parameters()[0].type();
          const typet &st=ct.parameters()[1].type();
          auto size_opt = size_of_expr(d.type(), ns);
          CHECK_RETURN(size_opt.has_value());
          const code_function_callt fc(
            mm_io_r,
            {typecast_exprt(d.pointer(), pt),
             typecast_exprt(size_opt.value(), st)});
          goto_function.body.insert_before_swap(it);
          *it = goto_programt::make_function_call(fc, source_location);
          it++;
        }
      }

      if(mm_io_w.is_not_nil())
      {
        if(a.lhs().id()==ID_dereference)
        {
          const dereference_exprt &d=to_dereference_expr(a.lhs());
          source_locationt source_location=it->source_location;
          const code_typet &ct=to_code_type(mm_io_w.type());
          const typet &pt=ct.parameters()[0].type();
          const typet &st=ct.parameters()[1].type();
          const typet &vt=ct.parameters()[2].type();
          auto size_opt = size_of_expr(d.type(), ns);
          CHECK_RETURN(size_opt.has_value());
          const code_function_callt fc(
            mm_io_w,
            {typecast_exprt(d.pointer(), pt),
             typecast_exprt(size_opt.value(), st),
             typecast_exprt(a.rhs(), vt)});
          goto_function.body.insert_before_swap(it);
          *it = goto_programt::make_function_call(fc, source_location);
          it++;
        }
      }
    }
  }
}

void mm_io(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  const namespacet ns(symbol_table);
  exprt mm_io_r=nil_exprt(), mm_io_w=nil_exprt();

  irep_idt id_r=CPROVER_PREFIX "mm_io_r";
  irep_idt id_w=CPROVER_PREFIX "mm_io_w";

  auto maybe_symbol=symbol_table.lookup(id_r);
  if(maybe_symbol)
    mm_io_r=maybe_symbol->symbol_expr();

  maybe_symbol=symbol_table.lookup(id_w);
  if(maybe_symbol)
    mm_io_w=maybe_symbol->symbol_expr();

  for(auto & f : goto_functions.function_map)
    mm_io(mm_io_r, mm_io_w, f.second, ns);
}

void mm_io(goto_modelt &model)
{
  mm_io(model.symbol_table, model.goto_functions);
}
