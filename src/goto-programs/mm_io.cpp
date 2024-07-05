/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation

#include "mm_io.h"

#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/replace_expr.h>

#include "goto_model.h"

#include <set>

class mm_iot
{
public:
  explicit mm_iot(symbol_table_baset &symbol_table);

  void mm_io(goto_functionst::goto_functiont &goto_function);

  std::size_t reads_replaced = 0;
  std::size_t writes_replaced = 0;

protected:
  const irep_idt id_r = CPROVER_PREFIX "mm_io_r";
  const irep_idt id_w = CPROVER_PREFIX "mm_io_w";

  const namespacet ns;
  exprt mm_io_r;
  exprt mm_io_r_value;
  exprt mm_io_w;
};

mm_iot::mm_iot(symbol_table_baset &symbol_table)
  : ns(symbol_table),
    mm_io_r(nil_exprt{}),
    mm_io_r_value(nil_exprt{}),
    mm_io_w(nil_exprt{})
{
  if(const auto mm_io_r_symbol = symbol_table.lookup(id_r))
  {
    mm_io_r = mm_io_r_symbol->symbol_expr();

    mm_io_r_value = get_fresh_aux_symbol(
                      to_code_type(mm_io_r.type()).return_type(),
                      id2string(id_r) + "$value",
                      id2string(id_r) + "$value",
                      mm_io_r_symbol->location,
                      mm_io_r_symbol->mode,
                      symbol_table)
                      .symbol_expr();
  }

  if(const auto mm_io_w_symbol = symbol_table.lookup(id_w))
    mm_io_w = mm_io_w_symbol->symbol_expr();
}

static std::set<dereference_exprt> collect_deref_expr(const exprt &src)
{
  std::set<dereference_exprt> collected;
  src.visit_pre([&collected](const exprt &e) {
    if(e.id() == ID_dereference)
      collected.insert(to_dereference_expr(e));
  });
  return collected;
}

void mm_iot::mm_io(goto_functionst::goto_functiont &goto_function)
{
  // return early when there is nothing to be done
  if(mm_io_r.is_nil() && mm_io_w.is_nil())
    return;

  for(auto it = goto_function.body.instructions.begin();
      it != goto_function.body.instructions.end();
      it++)
  {
    if(!it->is_assign())
      continue;

    auto &a_lhs = it->assign_lhs();
    auto &a_rhs = it->assign_rhs_nonconst();
    const auto deref_expr_r = collect_deref_expr(a_rhs);

    if(mm_io_r.is_not_nil())
    {
      if(deref_expr_r.size() == 1)
      {
        const dereference_exprt &d = *deref_expr_r.begin();
        source_locationt source_location = it->source_location();
        const code_typet &ct = to_code_type(mm_io_r.type());

        if_exprt if_expr(
          integer_address(d.pointer()),
          typecast_exprt::conditional_cast(mm_io_r_value, d.type()),
          d);
        replace_expr(d, if_expr, a_rhs);

        const typet &pt = ct.parameters()[0].type();
        const typet &st = ct.parameters()[1].type();
        auto size_opt = size_of_expr(d.type(), ns);
        CHECK_RETURN(size_opt.has_value());
        auto call = goto_programt::make_function_call(
          mm_io_r_value,
          mm_io_r,
          {typecast_exprt(d.pointer(), pt),
           typecast_exprt(size_opt.value(), st)},
          source_location);
        goto_function.body.insert_before_swap(it, call);
        ++reads_replaced;
        it++;
      }
    }

    if(mm_io_w.is_not_nil())
    {
      if(a_lhs.id() == ID_dereference)
      {
        const dereference_exprt &d = to_dereference_expr(a_lhs);
        source_locationt source_location = it->source_location();
        const code_typet &ct = to_code_type(mm_io_w.type());
        const typet &pt = ct.parameters()[0].type();
        const typet &st = ct.parameters()[1].type();
        const typet &vt = ct.parameters()[2].type();
        auto size_opt = size_of_expr(d.type(), ns);
        CHECK_RETURN(size_opt.has_value());
        const code_function_callt fc(
          mm_io_w,
          {typecast_exprt(d.pointer(), pt),
           typecast_exprt(size_opt.value(), st),
           typecast_exprt(a_rhs, vt)});
        goto_function.body.insert_before_swap(it);
        *it = goto_programt::make_function_call(fc, source_location);
        ++writes_replaced;
        it++;
      }
    }
  }
}

void mm_io(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  mm_iot rewrite{symbol_table};

  for(auto &f : goto_functions.function_map)
    rewrite.mm_io(f.second);

  if(rewrite.reads_replaced || rewrite.writes_replaced)
  {
    messaget log{message_handler};
    log.status() << "Replaced MMIO operations: " << rewrite.reads_replaced
                 << " read(s), " << rewrite.writes_replaced << " write(s)"
                 << messaget::eom;
  }
}

void mm_io(goto_modelt &model, message_handlert &message_handler)
{
  mm_io(model.symbol_table, model.goto_functions, message_handler);
}
