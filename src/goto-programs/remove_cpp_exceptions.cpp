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
#include <util/fresh_symbol.h>
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
  // the exception object being rethrown, so that the handlers it leaves do
  // not destroy it (null when none)
  symbol_exprt rethrown_ptr{irep_idt{}, typet{}};
  // thrown class types with a destructor: tag -> (destructor, class type)
  std::map<mp_integer, std::pair<symbol_exprt, typet>> tag_destructor;
  // the number of exceptions whose stack unwinding is running a destructor
  symbol_exprt unwinding_count{irep_idt{}, typet{}};

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

  /// Lower the handler-exit markers of the goto conversion: `cpp_end_catch'
  /// destroys the exception object of a handler that is left other than by
  /// rethrowing it ([except.throw]/5), `cpp_note_rethrow' records the
  /// exception being rethrown.
  void lower_handler_exits(goto_functionst &goto_functions);

  /// Call std::terminate where an exception leaves a function through which
  /// it must not propagate: the entry point (no handler was found,
  /// [except.handle]/9) and a function with a non-throwing exception
  /// specification ([except.spec]/5 of C++17, [except.terminate]/1.3).
  void terminate_on_escape(goto_functionst &goto_functions);

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

  void instrument_unwind_call(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it) override;

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

void remove_cpp_exceptionst::lower_handler_exits(
  goto_functionst &goto_functions)
{
  // the slots of all handlers with a parameter, so that a handler's exit can
  // see whether another active handler holds the same exception
  for(const auto &[name, function] : goto_functions.function_map)
  {
    (void)name;
    for(const auto &i : function.body.instructions)
    {
      const irep_idt handler =
        i.is_other() ? i.code().get("#cpp_handler") : irep_idt{};
      if(!handler.empty() && handler != ID_ellipsis)
        (void)get_handler_slot(handler);
    }
  }

  for(auto &[name, function] : goto_functions.function_map)
  {
    (void)name;
    goto_programt &body = function.body;
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        ++it)
    {
      if(!it->is_other())
        continue;
      const irep_idt &statement = it->code().get_statement();
      if(statement != "cpp_end_catch" && statement != "cpp_note_rethrow")
        continue;
      const source_locationt loc = it->source_location();
      // the handler's exception: its own slot, or (catch(...), a rethrow
      // outside the handler's body) the exception currently handled
      const irep_idt handler = it->code().get("#cpp_handler");
      symbol_exprt exc_ptr = current_exc_ptr;
      symbol_exprt exc_type = current_exc_type;
      if(!handler.empty() && handler != ID_ellipsis)
      {
        const auto slot = get_handler_slot(handler);
        exc_ptr = slot.first;
        exc_type = slot.second;
      }
      if(statement == "cpp_note_rethrow")
      {
        *it = goto_programt::make_assignment(rethrown_ptr, exc_ptr, loc);
        continue;
      }
      // cpp_end_catch: the handler is no longer active.  Unless the
      // exception is rethrown (its slot is read by the rethrow) or another
      // active handler holds it (this one is then not the last active
      // handler, [except.throw]/5), destroy the exception object by the
      // destructor of its (thrown) type.
      const null_pointer_exprt null{to_pointer_type(exc_ptr.type())};
      goto_programt tail;
      goto_programt::targett done = tail.add(goto_programt::make_skip(loc));
      goto_programt deactivate;
      goto_programt::targett deactivate_target =
        deactivate.add(goto_programt::make_skip(loc));
      if(exc_ptr != current_exc_ptr)
        deactivate.add(goto_programt::make_assignment(exc_ptr, null, loc));
      goto_programt dispatch;
      dispatch.add(goto_programt::make_goto(
        done,
        or_exprt{
          equal_exprt{exc_ptr, null}, equal_exprt{exc_ptr, rethrown_ptr}},
        loc));
      exprt::operandst held;
      for(const auto &other : handler_slots)
      {
        if(other.second.first != exc_ptr)
          held.push_back(equal_exprt{other.second.first, exc_ptr});
      }
      if(!held.empty())
      {
        dispatch.add(
          goto_programt::make_goto(deactivate_target, disjunction(held), loc));
      }
      for(const auto &[tag, destructor] : tag_destructor)
      {
        goto_programt call;
        goto_programt::targett next = call.add(goto_programt::make_skip(loc));
        goto_programt guarded;
        guarded.add(goto_programt::make_goto(
          next,
          notequal_exprt{exc_type, from_integer(tag, exc_type.type())},
          loc));
        code_function_callt destroy_call{
          destructor.first,
          {typecast_exprt{exc_ptr, pointer_type(destructor.second)}}};
        guarded.add(goto_programt::make_function_call(destroy_call, loc));
        guarded.destructive_append(call);
        dispatch.destructive_append(guarded);
      }
      dispatch.destructive_append(deactivate);
      dispatch.destructive_append(tail);
      *it = goto_programt::make_skip(loc);
      body.destructive_insert(std::next(it), dispatch);
    }
  }
}

/// The instructions that call std::terminate, which does not return
/// ([terminate.handler]/2): its model calls the handler, then assumes false;
/// without a declaration of std::terminate the default handler applies,
/// which calls abort() ([terminate.handler]/3), an assumption of false in
/// CBMC.
static void add_terminate(
  const symbol_table_baset &symbol_table,
  goto_programt &dest,
  const source_locationt &loc)
{
  if(const symbolt *terminate = symbol_table.lookup("std::terminate()"))
  {
    if(
      terminate->type.id() == ID_code &&
      to_code_type(terminate->type).parameters().empty())
    {
      dest.add(goto_programt::make_function_call(
        code_function_callt{terminate->symbol_expr()}, loc));
    }
  }
  dest.add(goto_programt::make_assumption(false_exprt{}, loc));
}

void remove_cpp_exceptionst::terminate_on_escape(
  goto_functionst &goto_functions)
{
  for(auto &[name, function] : goto_functions.function_map)
  {
    goto_programt &body = function.body;
    if(body.instructions.empty() || !body.instructions.back().is_end_function())
      continue;
    const symbolt *symbol = symbol_table.lookup(name);
    const bool entry_point = name == goto_functionst::entry_point();
    // N5008 [except.spec]/2: noexcept, noexcept(true) and throw() (C++17)
    // are non-throwing; noexcept(expression) is not evaluated
    // (#C_noexcept_unevaluated) and is left alone
    const bool non_throwing = symbol != nullptr &&
                              symbol->type.id() == ID_code &&
                              symbol->type.get_bool("#C_noexcept") &&
                              !symbol->type.get_bool("#C_noexcept_unevaluated");
    // std::terminate's model ends in an assumption of false
    if((!entry_point && !non_throwing) || name == "std::terminate()")
      continue;

    // The dispatch of an exception that no handler of this function
    // catches jumps to END_FUNCTION.  Turn END_FUNCTION into the check (the
    // jumps keep their target) and append the call and a new END_FUNCTION.
    goto_programt::targett end = std::prev(body.instructions.end());
    const source_locationt loc = end->source_location();
    goto_programt tail;
    add_terminate(symbol_table, tail, loc);
    goto_programt::targett new_end =
      tail.add(goto_programt::make_end_function(loc));
    *end = goto_programt::make_goto(new_end, no_inflight_exception(), loc);
    body.destructive_append(tail);
  }
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
    CPROVER_PREFIX "cpp_handler_exception$" + std::to_string(n),
    void_ptr,
    null_pointer_exprt(void_ptr));
  const symbol_exprt slot_type = make_global(
    CPROVER_PREFIX "cpp_handler_exception_type$" + std::to_string(n),
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
        // the destructor of a thrown class type, for the end of a handler
        const exprt value =
          uncaught_exceptions_domaint::get_exception_symbol(i.code());
        if(value.type().id() == ID_struct_tag && !tag_destructor.count(tag))
        {
          const symbolt *class_symbol = symbol_table.lookup(
            to_struct_tag_type(value.type()).get_identifier());
          if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
          {
            // member functions: in the methods of the class type, or (as the
            // C++ front end leaves them) among its components
            std::vector<struct_typet::componentt> functions =
              to_struct_type(class_symbol->type).components();
            for(const auto &m : class_symbol->type.find(ID_methods).get_sub())
              functions.push_back(
                static_cast<const struct_typet::componentt &>(m));
            for(const auto &c : functions)
            {
              if(
                c.type().id() == ID_code && !c.get_bool(ID_from_base) &&
                to_code_type(c.type()).return_type().id() == ID_destructor)
              {
                const symbolt *destructor = symbol_table.lookup(c.get_name());
                if(destructor != nullptr)
                {
                  tag_destructor.emplace(
                    tag,
                    std::make_pair(destructor->symbol_expr(), value.type()));
                }
                break;
              }
            }
          }
        }
      }
    }
  }

  if(!has_exceptions)
    return false;

  const pointer_typet void_ptr = pointer_type(empty_typet{});
  inflight_ptr = make_global(
    CPROVER_PREFIX "cpp_inflight_exception",
    void_ptr,
    null_pointer_exprt(void_ptr));
  inflight_type = make_global(
    CPROVER_PREFIX "cpp_inflight_exception_type",
    signed_int_type(),
    from_integer(0, signed_int_type()));
  current_exc_ptr = make_global(
    CPROVER_PREFIX "cpp_current_exception",
    void_ptr,
    null_pointer_exprt(void_ptr));
  current_exc_type = make_global(
    CPROVER_PREFIX "cpp_current_exception_type",
    signed_int_type(),
    from_integer(0, signed_int_type()));
  unwinding_count = make_global(
    CPROVER_PREFIX "cpp_unwinding_exceptions",
    signed_int_type(),
    from_integer(0, signed_int_type()));
  rethrown_ptr = make_global(
    CPROVER_PREFIX "cpp_rethrown_exception",
    void_ptr,
    null_pointer_exprt(void_ptr));
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
    // the rethrow leaves the handler, which is no longer active (its exit,
    // lower_handler_exits, ran before and kept the slot for this read)
    if(!handler_id.empty())
    {
      goto_program.insert_after(
        instr_it,
        goto_programt::make_assignment(
          src_ptr, null_pointer_exprt{to_pointer_type(src_ptr.type())}, loc));
    }
    goto_program.insert_after(
      instr_it, goto_programt::make_assignment(inflight_ptr, src_ptr, loc));
    return;
  }

  const typet thrown_type = value.type();

  const std::vector<irep_idt> ids = thrown_type_ids(*instr_it);
  const mp_integer tag = ids.empty() ? mp_integer{0} : type_tag[ids.front()];

  // per-throw-site static object holding a copy of the thrown value
  const irep_idt obj_name =
    CPROVER_PREFIX "cpp_exception_object$" + std::to_string(++object_counter);
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

/// A destructor called during stack unwinding ([except.ctor]/1-2) runs
/// while its exception is uncaught ([except.throw]/6, Note 4), but its own
/// body is ordinary code: the dispatch after each call in it must see the
/// in-flight state of exceptions thrown inside it only.  Save and clear the
/// in-flight exception around the call, and count the exception being
/// unwound (std::uncaught_exceptions reads the count).  A destructor that
/// exits via an exception here calls std::terminate ([except.terminate]/1.4),
/// which does not return ([terminate.handler]/2).
void remove_cpp_exceptionst::instrument_unwind_call(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it)
{
  const source_locationt loc = instr_it->source_location();
  const symbol_exprt saved_ptr = get_fresh_aux_symbol(
                                   inflight_ptr.type(),
                                   id2string(function_identifier),
                                   "unwound_exception",
                                   loc,
                                   ID_cpp,
                                   symbol_table)
                                   .symbol_expr();
  const symbol_exprt saved_type = get_fresh_aux_symbol(
                                    inflight_type.type(),
                                    id2string(function_identifier),
                                    "unwound_exception_type",
                                    loc,
                                    ID_cpp,
                                    symbol_table)
                                    .symbol_expr();
  const exprt one = from_integer(1, unwinding_count.type());

  goto_program.insert_before(
    instr_it, goto_programt::make_decl(saved_ptr, loc));
  goto_program.insert_before(
    instr_it, goto_programt::make_decl(saved_type, loc));
  goto_program.insert_before(
    instr_it, goto_programt::make_assignment(saved_ptr, inflight_ptr, loc));
  goto_program.insert_before(
    instr_it, goto_programt::make_assignment(saved_type, inflight_type, loc));
  goto_program.insert_before(
    instr_it,
    goto_programt::make_assignment(inflight_ptr, clear_inflight(), loc));
  goto_program.insert_before(
    instr_it,
    goto_programt::make_assignment(
      unwinding_count, plus_exprt{unwinding_count, one}, loc));

  // inserted after the call in reverse order
  goto_program.insert_after(
    instr_it, goto_programt::make_dead(saved_type, loc));
  goto_program.insert_after(instr_it, goto_programt::make_dead(saved_ptr, loc));
  goto_program.insert_after(
    instr_it,
    goto_programt::make_assignment(
      unwinding_count, minus_exprt{unwinding_count, one}, loc));
  goto_program.insert_after(
    instr_it, goto_programt::make_assignment(inflight_type, saved_type, loc));
  goto_program.insert_after(
    instr_it, goto_programt::make_assignment(inflight_ptr, saved_ptr, loc));
  // if the destructor exited via an exception: std::terminate(), which does
  // not return; inserted after the call in reverse order
  goto_programt::targett next = std::next(instr_it);
  goto_programt terminate;
  terminate.add(goto_programt::make_goto(next, no_inflight_exception(), loc));
  add_terminate(symbol_table, terminate, loc);
  goto_program.destructive_insert(next, terminate);
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
      // catch_var = *(T*)inflight_ptr; a reference ([except.handle]/15)
      // binds to the exception object: catch_var = (T*)inflight_ptr
      const typet var_type = catch_var.type();
      if(var_type.id() == ID_pointer && var_type.get_bool(ID_C_reference))
        it->assign_rhs_nonconst() = typecast_exprt(inflight_ptr, var_type);
      else
      {
        it->assign_rhs_nonconst() = dereference_exprt(
          typecast_exprt(inflight_ptr, pointer_type(var_type)));
      }
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
      // a handler of a rethrown exception destroys it ([except.throw]/5)
      goto_program.insert_after(
        it,
        goto_programt::make_assignment(
          rethrown_ptr,
          null_pointer_exprt{to_pointer_type(rethrown_ptr.type())},
          loc));
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
  // Inserted after the handler's first instruction, in reverse order; that
  // instruction becomes a SKIP so that it is not one of the handler's
  // statements (a destructor call, in the handlers of
  // add_constructor_unwinding), which ran with the exception still in
  // flight ([except.handle]/9: the handler is active once entered).
  if(!handler->is_skip())
  {
    goto_programt::instructiont original = *handler;
    goto_program.insert_after(handler, std::move(original));
    *handler = goto_programt::make_skip(handler->source_location());
  }
  goto_program.insert_after(
    handler,
    goto_programt::make_assignment(inflight_ptr, clear_inflight(), loc));
  goto_program.insert_after(
    handler,
    goto_programt::make_assignment(
      rethrown_ptr,
      null_pointer_exprt{to_pointer_type(rethrown_ptr.type())},
      loc));
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
  pass.lower_handler_exits(goto_model.goto_functions);
  pass(goto_model.goto_functions);
  pass.terminate_on_escape(goto_model.goto_functions);
  pass.initialize_globals(goto_model.goto_functions);
  goto_model.goto_functions.update();
}
