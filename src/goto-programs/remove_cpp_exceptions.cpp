/*******************************************************************\

Module: Remove C++ exceptions (goto-level lowering)

Author: Kiro

\*******************************************************************/

/// \file
/// Lower C++ exceptions (CATCH-PUSH/CATCH-POP/THROW) to ordinary control flow.

#include "remove_cpp_exceptions.h"

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_model.h>

#include <analyses/uncaught_exceptions_analysis.h>

#include <set>

/// Find the `side_effect_expr_throwt` inside a THROW instruction's code (the
/// code is a code_expressiont wrapping the throw side-effect).
static const exprt *find_throw_side_effect(const exprt &e)
{
  if(e.id() == ID_side_effect && e.get(ID_statement) == ID_throw)
    return &e;
  for(const auto &op : e.operands())
  {
    const exprt *r = find_throw_side_effect(op);
    if(r != nullptr)
      return r;
  }
  return nullptr;
}

/// The set of exception type-ids a `throw` matches -- the thrown type plus its
/// base classes (with a `_ptr` suffix for pointer types), as computed by
/// cpp_exception_list and stored on the throw side-effect's ID_exception_list.
static std::set<irep_idt> thrown_type_ids(const goto_programt::instructiont &i)
{
  std::set<irep_idt> ids;
  const exprt *se = find_throw_side_effect(i.code());
  if(se == nullptr)
    return ids;
  for(const auto &entry : se->find(ID_exception_list).get_sub())
    ids.insert(entry.id());
  return ids;
}

/// Create (once) a static symbol used to carry a thrown value from a `throw`
/// to the matching handler's parameter.  Keyed by the handler's catch
/// variable so that all throws reaching the same handler share the storage.
static symbol_exprt get_exception_storage(
  const symbol_exprt &catch_var,
  const irep_idt &mode,
  symbol_table_baset &symbol_table)
{
  const irep_idt id =
    id2string(catch_var.get_identifier()) + "#exception_storage";
  if(const symbolt *existing = symbol_table.lookup(id))
    return existing->symbol_expr();

  symbolt sym{id, catch_var.type(), mode};
  sym.base_name = id;
  sym.is_static_lifetime = true;
  sym.is_lvalue = true;
  sym.is_file_local = true;
  symbol_table.insert(std::move(sym));
  return symbol_exprt(id, catch_var.type());
}

/// Rewrite the handler's nondet initializer (`ASSIGN e := nondet`, emitted by
/// the front-end as a placeholder) into `ASSIGN e := <storage>`, so that the
/// handler parameter is bound to the thrown value carried in \p storage.
/// Returns true and sets \p catch_var when the handler declares a parameter.
static bool bind_handler_parameter(
  goto_programt &goto_program,
  goto_programt::targett handler,
  const irep_idt &mode,
  symbol_table_baset &symbol_table,
  symbol_exprt &storage_out)
{
  // The handler block begins with `DECL e`.
  if(!handler->is_decl())
    return false; // catch(...) or unnamed: no parameter to bind

  const symbol_exprt catch_var = handler->decl_symbol();

  storage_out = get_exception_storage(catch_var, mode, symbol_table);

  // Find the placeholder init `ASSIGN e := <nondet>` immediately following the
  // DECL and rewrite it to read from the storage.  Only rewrite once.
  goto_programt::targett it = std::next(handler);
  while(it != goto_program.instructions.end() && !it->is_assign())
    ++it;
  if(
    it != goto_program.instructions.end() && it->is_assign() &&
    it->assign_lhs() == catch_var &&
    it->assign_rhs().get_bool("#exception_catch_init"))
  {
    const typet catch_var_type = catch_var.type();
    it->assign_rhs_nonconst() =
      typecast_exprt::conditional_cast(storage_out, catch_var_type);
  }
  return true;
}

static void remove_cpp_exceptions_function(
  goto_programt &goto_program,
  const irep_idt &mode,
  symbol_table_baset &symbol_table)
{
  // Innermost-last stack of active catch clauses; each clause is the list of
  // (type-tag, handler-target) pairs of one try-block.
  using handlerst = std::vector<std::pair<irep_idt, goto_programt::targett>>;
  std::vector<handlerst> catch_stack;

  bool any = false;
  for(const auto &i : goto_program.instructions)
    if(i.is_catch() || i.is_throw())
    {
      any = true;
      break;
    }
  if(!any)
    return;

  Forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_catch())
    {
      const codet &code = it->code();
      if(code.get_statement() == ID_push_catch)
      {
        const code_push_catcht &pc = to_code_push_catch(code);
        const auto &exception_list = pc.exception_list();
        handlerst handlers;
        auto tgt = it->targets.begin();
        for(std::size_t k = 0;
            k < exception_list.size() && tgt != it->targets.end(); ++k, ++tgt)
        {
          handlers.emplace_back(exception_list[k].get_tag(), *tgt);
        }
        catch_stack.push_back(std::move(handlers));
      }
      else // pop
      {
        if(!catch_stack.empty())
          catch_stack.pop_back();
      }
      it->turn_into_skip();
    }
    else if(it->is_throw())
    {
      const std::set<irep_idt> ids = thrown_type_ids(*it);

      // Find the innermost matching handler: a catch clause whose tag is empty
      // (catch(...)) or is one of the thrown type-ids (base classes included).
      bool matched = false;
      goto_programt::targett handler;
      for(auto clause = catch_stack.rbegin();
          !matched && clause != catch_stack.rend(); ++clause)
      {
        for(const auto &h : *clause)
        {
          if(h.first.empty() || ids.count(h.first) != 0)
          {
            handler = h.second;
            matched = true;
            break;
          }
        }
      }

      if(!matched)
        continue; // propagates out of this function: left for a later phase

      const exprt value = uncaught_exceptions_domaint::get_exception_symbol(
        it->code());
      const source_locationt loc = it->source_location();

      symbol_exprt storage("", empty_typet{});
      if(bind_handler_parameter(
           goto_program, handler, mode, symbol_table, storage))
      {
        // store the thrown value, then jump to the handler
        *it = goto_programt::make_assignment(
          storage,
          typecast_exprt::conditional_cast(value, storage.type()),
          loc);
        goto_program.insert_after(
          it, goto_programt::make_goto(handler, loc));
        ++it; // skip the freshly inserted goto
      }
      else
      {
        // catch(...) with no parameter: just transfer control
        it->turn_into_skip();
        goto_program.insert_after(
          it, goto_programt::make_goto(handler, loc));
        ++it;
      }
    }
  }
}

void remove_cpp_exceptions(goto_modelt &goto_model, message_handlert &)
{
  for(auto &gf : goto_model.goto_functions.function_map)
  {
    const symbolt *fsym =
      goto_model.symbol_table.lookup(gf.first);
    const irep_idt mode = fsym != nullptr ? fsym->mode : ID_cpp;
    remove_cpp_exceptions_function(
      gf.second.body, mode, goto_model.symbol_table);
  }
  goto_model.goto_functions.update();
}
