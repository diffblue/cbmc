/*******************************************************************\

Module: Precise uninitialized variable check using shadow memory

Author: Kiro

\*******************************************************************/

/// \file
/// Instruments a goto model with shadow-memory-based uninitialized
/// variable checks.

#include "uninitialized_precise.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_cast.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol.h>

#include <goto-programs/goto_model.h>

#include <analyses/dirty.h>
#include <linking/static_lifetime_init.h>

static const irep_idt FIELD_NAME = "__uninit";
static unsigned tmp_counter = 0;

/// Build the field name argument in the format the C frontend uses:
/// cast(address_of(string[0]), void*)
static exprt field_name_arg()
{
  string_constantt str{FIELD_NAME};
  index_exprt idx{str, from_integer(0, c_index_type())};
  address_of_exprt addr{idx};
  return typecast_exprt{addr, pointer_type(empty_typet{})};
}

static exprt char_one()
{
  return from_integer(1, char_type());
}

static exprt char_zero()
{
  return from_integer(0, char_type());
}

/// Insert `__CPROVER_set_field(&lhs, FIELD_NAME, 1)` after \p target.
static void insert_set_field(
  goto_programt &body,
  goto_programt::targett target,
  const exprt &lhs)
{
  const auto loc = target->source_location();
  code_function_callt call{
    symbol_exprt{"__CPROVER_set_field", code_typet{{}, empty_typet{}}},
    {address_of_exprt{lhs}, field_name_arg(), char_one()}};
  call.add_source_location() = loc;
  body.insert_after(target, goto_programt::make_function_call(call, loc));
}

/// Insert `__CPROVER_set_field(ptr, FIELD_NAME, 1)` after \p target.
static void insert_set_field_ptr(
  goto_programt &body,
  goto_programt::targett target,
  const exprt &pointer)
{
  const auto loc = target->source_location();
  code_function_callt call{
    symbol_exprt{"__CPROVER_set_field", code_typet{{}, empty_typet{}}},
    {pointer, field_name_arg(), char_one()}};
  call.add_source_location() = loc;
  body.insert_after(target, goto_programt::make_function_call(call, loc));
}

/// Insert `tmp = get_field(&expr); assert(tmp == 1);` before \p target.
static void insert_check(
  goto_programt &body,
  goto_programt::targett target,
  const exprt &expr,
  const std::string &comment,
  symbol_table_baset &symbol_table,
  const irep_idt &mode)
{
  const auto loc = target->source_location();
  const irep_idt tmp_name = "__uninit_tmp_" + std::to_string(tmp_counter++);
  auxiliary_symbolt tmp_sym{tmp_name, char_type(), mode};
  tmp_sym.is_static_lifetime = false;
  tmp_sym.is_file_local = true;
  symbol_table.add(tmp_sym);
  symbol_exprt tmp_expr{tmp_name, char_type()};

  body.insert_before(target, goto_programt::make_decl(tmp_expr, loc));

  code_function_callt get_call{
    tmp_expr,
    symbol_exprt{"__CPROVER_get_field", code_typet{{}, char_type()}},
    {address_of_exprt{expr}, field_name_arg()}};
  get_call.add_source_location() = loc;
  body.insert_before(target, goto_programt::make_function_call(get_call, loc));

  source_locationt assert_loc = loc;
  assert_loc.set_comment(comment);
  assert_loc.set_property_class("uninitialized");
  body.insert_before(
    target,
    goto_programt::make_assertion(
      equal_exprt{tmp_expr, char_one()}, assert_loc));

  body.insert_before(target, goto_programt::make_dead(tmp_expr, loc));
}

void add_uninitialized_checks_precise(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns{goto_model.symbol_table};

  // Add shadow memory built-in symbols to the symbol table if not present.
  auto add_sm_symbol = [&](const irep_idt &name, const typet &return_type)
  {
    if(!goto_model.symbol_table.has_symbol(name))
    {
      code_typet fn_type{{}, return_type};
      fn_type.make_ellipsis();
      symbolt sym{name, fn_type, ID_C};
      sym.base_name = name;
      goto_model.symbol_table.add(sym);
    }
  };
  add_sm_symbol("__CPROVER_field_decl_local", empty_typet{});
  add_sm_symbol("__CPROVER_field_decl_global", empty_typet{});
  add_sm_symbol("__CPROVER_set_field", empty_typet{});
  add_sm_symbol("__CPROVER_get_field", signedbv_typet{32});

  // Add empty function bodies for field_decl built-ins (symex calls them
  // as regular functions; they need a body to enter/exit).
  for(const auto &name :
      {"__CPROVER_field_decl_local", "__CPROVER_field_decl_global"})
  {
    auto &fn = goto_model.goto_functions.function_map[name];
    if(fn.body.instructions.empty())
    {
      fn.body.add(goto_programt::make_end_function());
    }
  }

  // Insert field declaration at the end of __CPROVER_initialize
  // (after global variable init, before END_FUNCTION).
  {
    auto init_it =
      goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
    if(init_it != goto_model.goto_functions.function_map.end())
    {
      auto &body = init_it->second.body;
      for(auto it = body.instructions.begin(); it != body.instructions.end();
          ++it)
      {
        if(it->is_end_function())
        {
          code_function_callt decl_call{
            symbol_exprt{
              "__CPROVER_field_decl_local", code_typet{{}, empty_typet{}}},
            {field_name_arg(), char_zero()}};
          body.insert_before(
            it,
            goto_programt::make_function_call(
              decl_call, it->source_location()));
          break;
        }
      }
    }
  }

  for(auto &[fname, gf] : goto_model.goto_functions.function_map)
  {
    if(!gf.body_available())
      continue;

    auto &body = gf.body;
    const auto &fsym = ns.lookup(fname);

    // Run dirty analysis for this function when filtering.
    dirtyt dirty{gf};

    // Collect locals that need tracking.
    std::set<irep_idt> locals;
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        ++it)
    {
      if(!it->is_decl())
        continue;
      const auto &sym = it->decl_symbol();
      if(sym.type().id() == ID_code)
        continue;
      const auto &entry = ns.lookup(sym.get_identifier());
      if(entry.is_static_lifetime)
        continue;
      // In dirty_only mode, only track address-taken variables.
      if(!dirty(sym))
        continue;
      // Skip $tmp temporaries.
      if(id2string(entry.base_name).find("$tmp") != std::string::npos)
        continue;
      auto next = std::next(it);
      if(next != body.instructions.end())
      {
        bool init_at_decl = false;
        if(
          next->is_assign() && next->assign_lhs().id() == ID_symbol &&
          to_symbol_expr(next->assign_lhs()).get_identifier() ==
            sym.get_identifier())
        {
          bool rhs_reads_self = false;
          next->assign_rhs().visit_pre(
            [&](const exprt &e)
            {
              if(
                e.id() == ID_symbol &&
                to_symbol_expr(e).get_identifier() == sym.get_identifier())
              {
                rhs_reads_self = true;
              }
            });
          if(!rhs_reads_self)
            init_at_decl = true;
        }
        if(
          next->is_function_call() && next->call_lhs().id() == ID_symbol &&
          to_symbol_expr(next->call_lhs()).get_identifier() ==
            sym.get_identifier())
        {
          init_at_decl = true;
        }
        if(init_at_decl)
          continue;
      }
      locals.insert(sym.get_identifier());
    }

    // Collect targets to avoid iterator invalidation.
    std::vector<goto_programt::targett> targets;
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        ++it)
    {
      targets.push_back(it);
    }

    for(auto it : targets)
    {
      if(it->is_assign())
      {
        const auto &lhs = it->assign_lhs();
        const auto &rhs = it->assign_rhs();

        // Check reads in RHS (skip address_of subtrees).
        std::set<irep_idt> checked;
        std::function<void(const exprt &)> check_reads = [&](const exprt &e)
        {
          if(e.id() == ID_address_of)
            return;
          if(e.id() == ID_symbol)
          {
            const auto &id = to_symbol_expr(e).get_identifier();
            if(locals.count(id) && !checked.count(id))
            {
              checked.insert(id);
              const auto &entry = ns.lookup(id);
              insert_check(
                body,
                it,
                to_symbol_expr(e),
                "reading uninitialized local '" + id2string(entry.base_name) +
                  "'",
                goto_model.symbol_table,
                fsym.mode);
            }
          }
          for(const auto &op : e.operands())
            check_reads(op);
        };
        check_reads(rhs);

        // Set field after write to LHS.
        const exprt *cur = &lhs;
        while(cur->id() == ID_member || cur->id() == ID_index ||
              cur->id() == ID_byte_extract_little_endian ||
              cur->id() == ID_byte_extract_big_endian)
        {
          if(cur->id() == ID_member)
            cur = &to_member_expr(*cur).struct_op();
          else if(cur->id() == ID_index)
            cur = &to_index_expr(*cur).array();
          else
            cur = &to_byte_extract_expr(*cur).op();
        }

        if(cur->id() == ID_symbol)
        {
          const auto &id = to_symbol_expr(*cur).get_identifier();
          if(locals.count(id))
            insert_set_field(body, it, lhs);
        }
        else if(cur->id() == ID_dereference)
        {
          insert_set_field_ptr(body, it, to_dereference_expr(*cur).pointer());
        }
      }
      else if(it->is_function_call())
      {
        for(const auto &arg : it->call_arguments())
        {
          // Skip address-of arguments (passing &x is not a read of x)
          if(arg.id() == ID_address_of)
            continue;
          std::set<irep_idt> checked;
          arg.visit_pre(
            [&](const exprt &e)
            {
              if(e.id() == ID_symbol)
              {
                const auto &id = to_symbol_expr(e).get_identifier();
                if(locals.count(id) && !checked.count(id))
                {
                  checked.insert(id);
                  const auto &entry = ns.lookup(id);
                  insert_check(
                    body,
                    it,
                    to_symbol_expr(e),
                    "reading uninitialized local '" +
                      id2string(entry.base_name) + "'",
                    goto_model.symbol_table,
                    fsym.mode);
                }
              }
            });
        }

        if(it->call_lhs().is_not_nil() && it->call_lhs().id() == ID_symbol)
        {
          const auto &id = to_symbol_expr(it->call_lhs()).get_identifier();
          if(locals.count(id))
            insert_set_field(body, it, it->call_lhs());
        }
      }
    }
  }

  goto_model.goto_functions.update();
}
