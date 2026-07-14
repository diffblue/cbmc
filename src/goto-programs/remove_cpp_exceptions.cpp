/*******************************************************************\

Module: Remove C++ exceptions (goto-level lowering)

Author: Kiro

\*******************************************************************/

/// \file
/// Lower C++ exceptions (CATCH-PUSH/CATCH-POP/THROW) to ordinary control flow,
/// deriving from the language-agnostic remove_exceptions_baset.
///
/// C++ exceptions are value types matched by cpp_exception_id type tags.  The
/// in-flight exception is modelled by two globals: a pointer to the exception
/// object (null when none) and an integer type tag identifying the thrown
/// type.  A THROW copies the thrown value into a per-throw-site static object,
/// points the in-flight pointer at it and sets the tag; a handler copies the
/// value back into its parameter (through the tag-appropriate type) and clears
/// the pointer.  Handler matching (including base classes) uses the set of
/// thrown types whose cpp_exception_id list contains the handler's tag, which
/// is gathered from all THROW instructions in the program.

#include "remove_cpp_exceptions.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_exceptions_base.h>

#include <analyses/uncaught_exceptions_analysis.h>

#include <map>
#include <set>

/// Find the side_effect_expr_throwt inside a THROW instruction's code.
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

/// The list of exception type-ids a THROW matches (thrown type + base classes),
/// as computed by cpp_exception_list and stored on the throw side-effect.
static std::vector<irep_idt>
thrown_type_ids(const goto_programt::instructiont &i)
{
  std::vector<irep_idt> ids;
  const exprt *se = find_throw_side_effect(i.code());
  if(se == nullptr)
    return ids;
  for(const auto &entry : se->find(ID_exception_list).get_sub())
    ids.push_back(entry.id());
  return ids;
}

class remove_cpp_exceptionst : public remove_exceptions_baset
{
public:
  remove_cpp_exceptionst(
    symbol_table_baset &_symbol_table,
    function_may_throwt _function_may_throw,
    message_handlert &_message_handler)
    : remove_exceptions_baset(
        _symbol_table,
        std::move(_function_may_throw),
        _message_handler)
  {
  }

  /// Scan all throws to build the type-id tags and per-handler match sets, and
  /// create the in-flight globals.  Returns false if there are no exceptions.
  bool prepare(goto_functionst &goto_functions);

protected:
  symbol_exprt inflight_ptr{irep_idt{}, typet{}};
  symbol_exprt inflight_type{irep_idt{}, typet{}};
  // the exception currently being handled (saved on handler entry), used to
  // re-propagate on a rethrow (`throw;`)
  symbol_exprt current_exc_ptr{irep_idt{}, typet{}};
  symbol_exprt current_exc_type{irep_idt{}, typet{}};

  // Per-handler current-exception slots, keyed by the handler's catch-variable
  // identifier.  A handler writes its own slot on entry, so a nested/sibling
  // handler cannot clobber it; a bare `throw;` tagged with a handler id
  // re-propagates from that handler's slot ([except.throw]/8).  (ptr, type)
  std::map<irep_idt, std::pair<symbol_exprt, symbol_exprt>> handler_slots;

  // Get-or-create the (ptr, type) slot globals for handler \p id.
  std::pair<symbol_exprt, symbol_exprt> get_handler_slot(const irep_idt &id);

  // cpp_exception_id string -> integer tag (assigned to thrown primary types)
  std::map<irep_idt, mp_integer> type_tag;
  // handler tag -> set of thrown-type integer tags it catches (base classes
  // included)
  std::map<irep_idt, std::set<mp_integer>> handler_matches;
  std::size_t object_counter = 0;

  // globals created by this pass with their initial values; their
  // initializations must be appended to __CPROVER_initialize, which was
  // generated before this pass ran (an uninitialized in-flight global reads
  // as nondet and derails the dispatch)
  std::vector<std::pair<symbol_exprt, exprt>> created_globals;

public:
  /// Append initializations of the globals this pass created to
  /// __CPROVER_initialize (no-op if that function is not in the model).
  void initialize_globals(goto_functionst &goto_functions);

protected:
  symbol_exprt get_inflight_exception_global() override
  {
    return inflight_ptr;
  }

  exprt no_inflight_exception() override
  {
    return equal_exprt(
      inflight_ptr, null_pointer_exprt(to_pointer_type(inflight_ptr.type())));
  }

  void add_handler_dispatch(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const irep_idt &tag,
    const goto_programt::targett &handler_target) override;

  void set_inflight_exception(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it) override;

  // C++ has no landing-pad instruction; handler binding is done in
  // prepare_handler at the handler entry.
  void instrument_exception_handler(
    goto_programt &,
    const goto_programt::targett &instr_it,
    bool) override
  {
    instr_it->turn_into_skip();
  }

  void prepare_handler(
    goto_programt &goto_program,
    const goto_programt::targett &handler) override;

  symbol_exprt make_global(
    const irep_idt &name,
    const typet &type,
    const exprt &initial_value);

  exprt clear_inflight() const
  {
    return null_pointer_exprt(to_pointer_type(inflight_ptr.type()));
  }
};

symbol_exprt remove_cpp_exceptionst::make_global(
  const irep_idt &name,
  const typet &type,
  const exprt &initial_value)
{
  if(const symbolt *existing = symbol_table.lookup(name))
    return existing->symbol_expr();
  symbolt sym{name, type, ID_cpp};
  sym.base_name = name;
  sym.is_static_lifetime = true;
  sym.is_lvalue = true;
  sym.value = initial_value;
  symbol_table.insert(std::move(sym));
  symbol_exprt result{name, type};
  if(initial_value.is_not_nil())
    created_globals.emplace_back(result, initial_value);
  return result;
}

void remove_cpp_exceptionst::initialize_globals(goto_functionst &goto_functions)
{
  // CPROVER_PREFIX "initialize" (INITIALIZE_FUNCTION in linking/, which this
  // module cannot depend on)
  auto init_it = goto_functions.function_map.find(CPROVER_PREFIX "initialize");
  if(init_it == goto_functions.function_map.end())
    return;

  goto_programt &init_body = init_it->second.body;
  if(init_body.instructions.empty())
    return;
  // insert at the very front: __CPROVER_initialize may call C++ dynamic
  // initialization, whose instrumented dispatches already read the globals
  goto_programt::targett front = init_body.instructions.begin();
  const source_locationt loc = front->source_location();

  for(const auto &[global, value] : created_globals)
  {
    init_body.insert_before(
      front, goto_programt::make_assignment(global, value, loc));
  }
}

std::pair<symbol_exprt, symbol_exprt>
remove_cpp_exceptionst::get_handler_slot(const irep_idt &id)
{
  auto found = handler_slots.find(id);
  if(found != handler_slots.end())
    return found->second;

  const std::size_t n = handler_slots.size();
  const pointer_typet void_ptr = pointer_type(empty_typet{});
  const symbol_exprt slot_ptr = make_global(
    "__CPROVER_cpp_handler_exception$" + std::to_string(n),
    void_ptr,
    null_pointer_exprt(void_ptr));
  const symbol_exprt slot_type = make_global(
    "__CPROVER_cpp_handler_exception_type$" + std::to_string(n),
    signed_int_type(),
    from_integer(0, signed_int_type()));
  auto result = std::make_pair(slot_ptr, slot_type);
  handler_slots.emplace(id, result);
  return result;
}

bool remove_cpp_exceptionst::prepare(goto_functionst &goto_functions)
{
  bool has_exceptions = false;
  for(const auto &gf : goto_functions.function_map)
  {
    for(const auto &i : gf.second.body.instructions)
    {
      if(i.is_catch())
        has_exceptions = true;
      if(i.is_throw())
      {
        has_exceptions = true;
        const std::vector<irep_idt> ids = thrown_type_ids(i);
        if(ids.empty())
          continue;
        // assign the primary (thrown) type an integer tag
        auto inserted =
          type_tag.emplace(ids.front(), mp_integer{(long long)type_tag.size()});
        const mp_integer tag = inserted.first->second;
        // this thrown type is caught by handlers for any of its ids (the
        // thrown type itself or a base class)
        for(const auto &id : ids)
          handler_matches[id].insert(tag);
      }
    }
  }

  if(!has_exceptions)
    return false;

  const pointer_typet void_ptr = pointer_type(empty_typet{});
  inflight_ptr = make_global(
    "__CPROVER_cpp_inflight_exception", void_ptr, null_pointer_exprt(void_ptr));
  inflight_type = make_global(
    "__CPROVER_cpp_inflight_exception_type",
    signed_int_type(),
    from_integer(0, signed_int_type()));
  current_exc_ptr = make_global(
    "__CPROVER_cpp_current_exception", void_ptr, null_pointer_exprt(void_ptr));
  current_exc_type = make_global(
    "__CPROVER_cpp_current_exception_type",
    signed_int_type(),
    from_integer(0, signed_int_type()));
  return true;
}

void remove_cpp_exceptionst::add_handler_dispatch(
  const irep_idt &,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const irep_idt &tag,
  const goto_programt::targett &handler_target)
{
  auto it = handler_matches.find(tag);
  if(it == handler_matches.end() || it->second.empty())
    return; // no thrown type matches this handler -- unreachable, emit nothing

  // guard: inflight_type is one of the tags this handler catches
  exprt::operandst disjuncts;
  for(const mp_integer &m : it->second)
  {
    disjuncts.push_back(
      equal_exprt(inflight_type, from_integer(m, inflight_type.type())));
  }
  const exprt guard = disjunction(disjuncts);

  goto_program.insert_after(
    instr_it,
    goto_programt::make_goto(
      handler_target, guard, instr_it->source_location()));
}

void remove_cpp_exceptionst::set_inflight_exception(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it)
{
  const source_locationt loc = instr_it->source_location();
  const exprt value =
    uncaught_exceptions_domaint::get_exception_symbol(instr_it->code());

  // A rethrow (`throw;`) has no operand -- get_exception_symbol returns the
  // throw side-effect itself.  Re-propagate the exception currently being
  // handled ([except.throw]/8) instead of constructing a new object.
  if(
    value.id() == ID_side_effect &&
    to_side_effect_expr(value).get_statement() == ID_throw)
  {
    // A rethrow lexically inside a handler is tagged with that handler's id;
    // re-propagate from that handler's own slot so a nested/sibling handler
    // cannot have clobbered it.  Untagged rethrows (e.g. in a callee, or in a
    // catch(...) with no catch variable) fall back to the shared globals.
    symbol_exprt src_type = current_exc_type;
    symbol_exprt src_ptr = current_exc_ptr;
    const irep_idt handler_id = value.get("#rethrow_handler");
    if(!handler_id.empty())
    {
      const auto slot = get_handler_slot(handler_id);
      src_ptr = slot.first;
      src_type = slot.second;
    }

    *instr_it = goto_programt::make_assignment(inflight_type, src_type, loc);
    goto_program.insert_after(
      instr_it, goto_programt::make_assignment(inflight_ptr, src_ptr, loc));
    return;
  }

  const typet thrown_type = value.type();

  const std::vector<irep_idt> ids = thrown_type_ids(*instr_it);
  const mp_integer tag = ids.empty() ? mp_integer{0} : type_tag[ids.front()];

  // per-throw-site static object holding a copy of the thrown value
  const irep_idt obj_name =
    "__CPROVER_cpp_exception_object$" + std::to_string(++object_counter);
  const symbol_exprt exc_obj = make_global(obj_name, thrown_type, nil_exprt{});

  // exc_obj = value
  *instr_it = goto_programt::make_assignment(exc_obj, value, loc);
  // inflight_ptr = (void*)&exc_obj  (inserted after -> runs next)
  goto_program.insert_after(
    instr_it,
    goto_programt::make_assignment(
      inflight_ptr,
      typecast_exprt(address_of_exprt(exc_obj), inflight_ptr.type()),
      loc));
  // inflight_type = tag
  goto_program.insert_after(
    instr_it,
    goto_programt::make_assignment(
      inflight_type, from_integer(tag, inflight_type.type()), loc));
}

void remove_cpp_exceptionst::prepare_handler(
  goto_programt &goto_program,
  const goto_programt::targett &handler)
{
  const source_locationt loc = handler->source_location();

  if(handler->is_decl())
  {
    const symbol_exprt catch_var = handler->decl_symbol();

    // find the placeholder `catch_var = nondet` init after the DECL
    goto_programt::targett it = std::next(handler);
    while(it != goto_program.instructions.end() && !it->is_assign())
      ++it;
    if(
      it != goto_program.instructions.end() && it->is_assign() &&
      it->assign_lhs() == catch_var &&
      it->assign_rhs().get_bool("#exception_catch_init"))
    {
      // catch_var = *(T*)inflight_ptr
      const typet var_type = catch_var.type();
      it->assign_rhs_nonconst() =
        dereference_exprt(typecast_exprt(inflight_ptr, pointer_type(var_type)));
      // preserve the exception being handled (for a potential rethrow), then
      // clear the in-flight exception.  In addition to the shared globals
      // (used by rethrows in callees / catch(...)), write this handler's own
      // slot so a rethrow lexically inside it re-propagates the right
      // exception even after a nested handler ran.  Inserted after `it` in
      // reverse program order.
      const auto slot = get_handler_slot(catch_var.get_identifier());
      goto_program.insert_after(
        it,
        goto_programt::make_assignment(inflight_ptr, clear_inflight(), loc));
      goto_program.insert_after(
        it, goto_programt::make_assignment(slot.first, inflight_ptr, loc));
      goto_program.insert_after(
        it, goto_programt::make_assignment(slot.second, inflight_type, loc));
      goto_program.insert_after(
        it, goto_programt::make_assignment(current_exc_ptr, inflight_ptr, loc));
      goto_program.insert_after(
        it,
        goto_programt::make_assignment(current_exc_type, inflight_type, loc));
      return;
    }
  }

  // catch(...) or no bindable parameter: preserve the exception being handled
  // (for a potential rethrow) and clear the in-flight exception on entry.
  // Inserted after the handler's first instruction, in reverse order.
  goto_program.insert_after(
    handler,
    goto_programt::make_assignment(inflight_ptr, clear_inflight(), loc));
  goto_program.insert_after(
    handler,
    goto_programt::make_assignment(current_exc_ptr, inflight_ptr, loc));
  goto_program.insert_after(
    handler,
    goto_programt::make_assignment(current_exc_type, inflight_type, loc));
}

void remove_cpp_exceptions(goto_modelt &goto_model, message_handlert &msg)
{
  // Conservatively treat every function as possibly-throwing, so every call
  // site gets an exception dispatch.  A sound over-approximation that only
  // instruments call sites of possibly-throwing callees (transitive "contains a
  // THROW") was tried, but the per-call `inflight == null` dispatch guards turn
  // out to prune the solver's state space significantly on exception-heavy STL
  // code; dropping them for provably non-throwing calls caused a large formula
  // blow-up (e.g. std::deque tests running out of memory).  The saving in
  // instructions did not outweigh the lost pruning, so the dispatch is kept
  // unconditional.
  remove_exceptions_baset::function_may_throwt function_may_throw =
    [](const irep_idt &) { return true; };

  remove_cpp_exceptionst pass(goto_model.symbol_table, function_may_throw, msg);
  if(!pass.prepare(goto_model.goto_functions))
    return; // no exceptions: nothing to do
  pass(goto_model.goto_functions);
  pass.initialize_globals(goto_model.goto_functions);
  goto_model.goto_functions.update();
}
