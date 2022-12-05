/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

// TODO apply loop contracts transformations as part of function instrumentation

#include "dfcc_instrument.h"

#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/suffix.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <ansi-c/c_expr.h>
#include <ansi-c/c_object_factory_parameters.h>
#include <goto-instrument/contracts/cfg_info.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/generate_function_bodies.h>
#include <langapi/language_util.h>

#include "dfcc_is_freeable.h"
#include "dfcc_is_fresh.h"
#include "dfcc_library.h"
#include "dfcc_obeys_contract.h"
#include "dfcc_utils.h"

#include <memory>

std::set<irep_idt> dfcc_instrumentt::function_cache;

dfcc_instrumentt::dfcc_instrumentt(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library)
  : goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    ns(goto_model.symbol_table)
{
  // these come from different assert.h implementation on different systems
  // and eventually become ASSERT instructions and must not be instrumented
  internal_symbols.insert("__assert_fail");
  internal_symbols.insert("_assert");
  internal_symbols.insert("__assert_c99");
  internal_symbols.insert("_wassert");
  internal_symbols.insert("__assert_rtn");
  internal_symbols.insert("__assert");
  internal_symbols.insert("__assert_func");

  /// These builtins are translated to no-ops and must not be instrumented
  internal_symbols.insert("__builtin_prefetch");
  internal_symbols.insert("__builtin_unreachable");

  /// These builtins are valist management functions
  /// and interpreted natively in src/goto-symex/symex_builtin_functions.cpp
  /// and must not be instrumented
  internal_symbols.insert(ID_gcc_builtin_va_arg);
  internal_symbols.insert("__builtin_va_copy");
  internal_symbols.insert("__builtin_va_start");
  internal_symbols.insert("__va_start");
  internal_symbols.insert("__builtin_va_end");

  /// These builtins get translated to CPROVER equivalents
  /// and must not be instrumented
  internal_symbols.insert("__builtin_isgreater");
  internal_symbols.insert("__builtin_isgreaterequal");
  internal_symbols.insert("__builtin_isless");
  internal_symbols.insert("__builtin_islessequal");
  internal_symbols.insert("__builtin_islessgreater");
  internal_symbols.insert("__builtin_isunordered");
}

void dfcc_instrumentt::get_instrumented_functions(
  std::set<irep_idt> &dest) const
{
  dest.insert(
    dfcc_instrumentt::function_cache.begin(),
    dfcc_instrumentt::function_cache.end());
}

/*
  A word on built-ins:

  C compiler builtins are declared in
  - src/ansi-c/clang_builtin_headers*.h
  - src/ansi-c/gcc_builtin_headers*.h
  - src/ansi-c/windows_builtin_headers.h

  Some gcc builtins are compiled down to goto instructions
  and inlined in place during type-checking:
  - src/ansi-c/c_typecheck_gcc_polymorphic_builtins.cpp
  - src/ansi-c/c_typecheck_expr.cpp, method do_special_functions
  so they essentially disappear from the model.

  Builtins are also handled in:
  - src/goto-programs/builtin_functions.cpp
  - src/goto-symex/symex_builtin_functions.cpp

  Some compiler builtins have implementations defined as C functions in the
  cprover library, and these should be instrumented just like other functions.

  Last, some compiler built-ins might have just a declaration but
  no conversion or library implementation.
  They might then persist in the program as functions which return a nondet
  value or transformed into side_effect_nondet_exprt during conversion
  If they survive as functions we should be able to add an extra parameter
  to these functions even if they have no body.

  The CPROVER built-ins are declared here:
  - src/ansi-c/cprover_builtin_headers.h
  - src/ansi-c/cprover_library.h
  - src/ansi-c/library/cprover_contracts.c
  and should not be instrumented.

  The case of __CPROVER_deallocate is special: it is a wrapper for an assignment
  to the __CPROVER_deallocated_object global. We do not want to
  instrument this function, but we still want to check that its parameters
  are allowed for deallocation by the write set.

  There is also a number of CPROVER global static symbols that are used to
  suport memory safety property instrumentation, and assignments to these
  statics should always be allowed (i.e not instrumented):
  - __CPROVER_alloca_object,
  - __CPROVER_dead_object,
  - __CPROVER_deallocated,
  - __CPROVER_malloc_is_new_array,
  - __CPROVER_max_malloc_size,
  - __CPROVER_memory_leak,
  - __CPROVER_new_object,
  - __CPROVER_next_thread_id,
  - __CPROVER_next_thread_key,
  - __CPROVER_pipe_count,
  - __CPROVER_rounding_mode,
  - __CPROVER_thread_id,
  - __CPROVER_thread_key_dtors,
  - __CPROVER_thread_keys,
  - __CPROVER_threads_exited,
  -  ... (and more of them)

  /// These have a library implementation and must be instrumented
  static std::set<irep_idt> alloca_builtins = {"alloca", "__builtin_alloca"};

  /// These built-ins have CPROVER library implementation, can be instrumented
  static std::set<std::string> builtins_with_cprover_impl = {
    "__builtin_ia32_sfence",
    "__builtin_ia32_lfence",
    "__builtin_ia32_mfence",
    "__builtin_ffs",
    "__builtin_ffsl",
    "__builtin_ffsll",
    "__builtin_ia32_vec_ext_v4hi",
    "__builtin_ia32_vec_ext_v8hi",
    "__builtin_ia32_vec_ext_v4si",
    "__builtin_ia32_vec_ext_v2di",
    "__builtin_ia32_vec_ext_v16qi",
    "__builtin_ia32_vec_ext_v4sf",
    "__builtin_ia32_psubsw128",
    "__builtin_ia32_psubusw128",
    "__builtin_ia32_paddsw",
    "__builtin_ia32_psubsw",
    "__builtin_ia32_vec_init_v4hi",
    "__builtin_flt_rounds",
    "__builtin_fabs",
    "__builtin_fabsl",
    "__builtin_fabsf",
    "__builtin_inff",
    "__builtin_inf",
    "__builtin_infl",
    "__builtin_isinf",
    "__builtin_isinff",
    "__builtin_isinf",
    "__builtin_isnan",
    "__builtin_isnanf",
    "__builtin_huge_valf",
    "__builtin_huge_val",
    "__builtin_huge_vall",
    "__builtin_nan",
    "__builtin_nanf",
    "__builtin_abs",
    "__builtin_labs",
    "__builtin_llabs",
    "__builtin_alloca",
    "__builtin___strcpy_chk",
    "__builtin___strcat_chk",
    "__builtin___strncat_chk",
    "__builtin___strncpy_chk",
    "__builtin___memcpy_chk",
    "__builtin_memset",
    "__builtin___memset_chk",
    "__builtin___memmove_chk"};
*/

/// True iff the symbol must not be instrumented
bool dfcc_instrumentt::is_internal_symbol(const irep_idt &id) const
{
  return internal_symbols.find(id) != internal_symbols.end();
}

/// True if id has `CPROVER_PREFIX` or `__VERIFIER` or `nondet` prefix,
/// or an `&object` suffix (cf system_library_symbols.cpp)
bool dfcc_instrumentt::is_cprover_symbol(const irep_idt &id) const
{
  std::string str = id2string(id);
  return has_prefix(str, CPROVER_PREFIX) || has_prefix(str, "__VERIFIER") ||
         has_prefix(str, "nondet") || has_suffix(str, "$object");
}

bool dfcc_instrumentt::do_not_instrument(const irep_idt &id) const
{
  return !has_prefix(id2string(id), CPROVER_PREFIX "file_local") &&
         (is_cprover_symbol(id) || is_internal_symbol(id));
}

void dfcc_instrumentt::instrument_harness_function(
  const irep_idt &function_id,
  std::set<irep_idt> &function_pointer_contracts)
{
  bool inserted = dfcc_instrumentt::function_cache.insert(function_id).second;
  if(!inserted)
    return;

  const null_pointer_exprt null_expr(
    to_pointer_type(library.dfcc_type[dfcc_typet::WRITE_SET_PTR]));

  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);
  auto &body = goto_function.body;

  // rewrite is_fresh_calls
  dfcc_is_fresht is_fresh(library, message_handler);
  is_fresh.rewrite_calls(body, null_expr);

  // rewrite is_freeable/was_freed calls
  dfcc_is_freeablet is_freeable(library, message_handler);
  is_freeable.rewrite_calls(body, null_expr);

  // rewrite obeys_contract calls
  dfcc_obeys_contractt obeys_contract(library, message_handler);
  obeys_contract.rewrite_calls(body, null_expr, function_pointer_contracts);

  // rewrite calls
  Forall_goto_program_instructions(it, body)
  {
    if(it->is_function_call())
      instrument_call_instruction(null_expr, it, body);
  }

  goto_model.goto_functions.update();
}

std::set<symbol_exprt>
dfcc_instrumentt::get_local_statics(const irep_idt &function_id)
{
  std::set<symbol_exprt> local_statics;
  for(const auto &sym_pair : goto_model.symbol_table)
  {
    const auto &sym = sym_pair.second;
    if(sym.is_static_lifetime)
    {
      const auto &loc = sym.location;
      if(!loc.get_function().empty() && loc.get_function() == function_id)
      {
        local_statics.insert(sym.symbol_expr());
      }
    }
  }
  return local_statics;
}

void dfcc_instrumentt::instrument_function(
  const irep_idt &function_id,
  std::set<irep_idt> &function_pointer_contracts)
{
  // use same name for local static search
  instrument_function(function_id, function_id, function_pointer_contracts);
}

void dfcc_instrumentt::instrument_wrapped_function(
  const irep_idt &wrapped_function_id,
  const irep_idt &initial_function_id,
  std::set<irep_idt> &function_pointer_contracts)
{
  // use the initial name name for local static search
  instrument_function(
    wrapped_function_id, initial_function_id, function_pointer_contracts);
}

void dfcc_instrumentt::instrument_function(
  const irep_idt &function_id,
  const irep_idt &function_id_for_local_static_search,
  std::set<irep_idt> &function_pointer_contracts)
{
  // never instrument a function twice
  bool inserted = dfcc_instrumentt::function_cache.insert(function_id).second;
  if(!inserted)
    return;

  auto found = goto_model.goto_functions.function_map.find(function_id);
  PRECONDITION_WITH_DIAGNOSTICS(
    found != goto_model.goto_functions.function_map.end(),
    "Function '" + id2string(function_id) + "' must exist in the model.");

  auto &goto_function = found->second;

  function_cfg_infot cfg_info(goto_function);

  const auto &write_set = utils.add_parameter(
    function_id,
    "__write_set_to_check",
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR]);

  std::set<symbol_exprt> local_statics =
    get_local_statics(function_id_for_local_static_search);

  instrument_function_body(
    function_id,
    write_set.symbol_expr(),
    cfg_info,
    local_statics,
    function_pointer_contracts);
}

void dfcc_instrumentt::instrument_function_body(
  const irep_idt &function_id,
  const exprt &write_set,
  cfg_infot &cfg_info,
  const std::set<symbol_exprt> &local_statics,
  std::set<irep_idt> &function_pointer_contracts)
{
  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  if(!goto_function.body_available())
  {
    // generate a default body `assert(false);assume(false);`
    std::string options = "assert-false-assume-false";
    c_object_factory_parameterst object_factory_params;
    auto generate_function_bodies = generate_function_bodies_factory(
      options, object_factory_params, goto_model.symbol_table, message_handler);
    generate_function_bodies->generate_function_body(
      goto_function, goto_model.symbol_table, function_id);
    return;
  }

  auto &body = goto_function.body;

  // instrument the whole body
  instrument_instructions(
    function_id,
    write_set,
    body,
    body.instructions.begin(),
    body.instructions.end(),
    cfg_info,
    // don't skip any instructions
    {},
    function_pointer_contracts);

  // insert add/remove instructions for local statics
  auto begin = body.instructions.begin();
  auto end = std::prev(body.instructions.end());

  for(const auto &local_static : local_statics)
  {
    // automatically add local statics to the write set
    insert_add_allocated_call(
      function_id, write_set, local_static, begin, body);

    // automatically remove local statics to the write set
    insert_record_dead_call(function_id, write_set, local_static, end, body);
  }

  // cleanup
  remove_skip(body);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // add loop ids
  goto_model.goto_functions.compute_loop_numbers();
}

void dfcc_instrumentt::instrument_goto_program(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const exprt &write_set,
  std::set<irep_idt> &function_pointer_contracts)
{
  goto_program_cfg_infot cfg_info(goto_program);

  instrument_instructions(
    function_id,
    write_set,
    goto_program,
    goto_program.instructions.begin(),
    goto_program.instructions.end(),
    cfg_info,
    // no pred, don't skip any instructions
    {},
    function_pointer_contracts);

  // cleanup
  remove_skip(goto_program);
}

void dfcc_instrumentt::instrument_instructions(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt &goto_program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  cfg_infot &cfg_info,
  const std::function<bool(const goto_programt::targett &)> &pred,
  std::set<irep_idt> &function_pointer_contracts)
{
  // rewrite is_fresh calls
  dfcc_is_fresht is_fresh(library, message_handler);
  is_fresh.rewrite_calls(
    goto_program, first_instruction, last_instruction, write_set);

  // rewrite is_freeable/was_freed calls
  dfcc_is_freeablet is_freeable(library, message_handler);
  is_freeable.rewrite_calls(
    goto_program, first_instruction, last_instruction, write_set);

  // rewrite obeys_contract calls
  dfcc_obeys_contractt obeys_contract(library, message_handler);
  obeys_contract.rewrite_calls(
    goto_program,
    first_instruction,
    last_instruction,
    write_set,
    function_pointer_contracts);

  const namespacet ns(goto_model.symbol_table);
  auto &target = first_instruction;

  // excluding the last
  while(target != last_instruction)
  {
    // Skip instructions marked as disabled for assigns clause checking
    // or rejected by the predicate
    if(pred && !pred(target))
    {
      target++;
      continue;
    }

    if(target->is_decl())
    {
      instrument_decl(function_id, write_set, target, goto_program, cfg_info);
    }
    if(target->is_dead())
    {
      instrument_dead(function_id, write_set, target, goto_program, cfg_info);
    }
    else if(target->is_assign())
    {
      instrument_assign(function_id, write_set, target, goto_program, cfg_info);
    }
    else if(target->is_function_call())
    {
      instrument_function_call(
        function_id, write_set, target, goto_program, cfg_info);
    }
    else if(target->is_other())
    {
      instrument_other(function_id, write_set, target, goto_program, cfg_info);
    }
    // else do nothing
    target++;
  }
}

bool dfcc_instrumentt::must_track_decl_or_dead(
  const goto_programt::targett &target,
  const cfg_infot &cfg_info) const
{
  INVARIANT(
    target->is_decl() || target->is_dead(),
    "Target must be a DECL or DEAD instruction");

  const auto &ident = target->is_decl()
                        ? target->decl_symbol().get_identifier()
                        : target->dead_symbol().get_identifier();
  bool retval = cfg_info.is_not_local_or_dirty_local(ident);

  return retval;
}

void dfcc_instrumentt::insert_add_allocated_call(
  const irep_idt &function_id,
  const exprt &write_set,
  const symbol_exprt &symbol_expr,
  goto_programt::targett &target,
  goto_programt &goto_program)
{
  goto_programt payload;
  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), target->source_location()));

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_ADD_ALLOCATED].symbol_expr(),
      {write_set, address_of_exprt(symbol_expr)}},
    target->source_location()));

  auto label_instruction =
    payload.add(goto_programt::make_skip(target->source_location()));
  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
}

/// \details
/// ```c
/// DECL x;
/// ----
/// insert_add_allocated_call(...);
/// ```
void dfcc_instrumentt::instrument_decl(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  if(!must_track_decl_or_dead(target, cfg_info))
    return;

  const auto &decl_symbol = target->decl_symbol();
  target++;
  insert_add_allocated_call(
    function_id, write_set, decl_symbol, target, goto_program);
  target--;
}

void dfcc_instrumentt::insert_record_dead_call(
  const irep_idt &function_id,
  const exprt &write_set,
  const symbol_exprt &symbol_expr,
  goto_programt::targett &target,
  goto_programt &goto_program)
{
  goto_programt payload;

  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), target->source_location()));

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RECORD_DEAD].symbol_expr(),
      {write_set, address_of_exprt(symbol_expr)}},
    target->source_location()));

  auto label_instruction =
    payload.add(goto_programt::make_skip(target->source_location()));

  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
}

/// \details
/// ```c
/// insert_record_dead_call(...);
/// ----
/// DEAD x;
/// ```
void dfcc_instrumentt::instrument_dead(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  if(!must_track_decl_or_dead(target, cfg_info))
    return;

  const auto &decl_symbol = target->dead_symbol();
  insert_record_dead_call(
    function_id, write_set, decl_symbol, target, goto_program);
}

bool dfcc_instrumentt::must_check_lhs(
  const source_locationt &lhs_source_location,
  source_locationt &check_source_location,
  const irep_idt &language_mode,
  const exprt &lhs,
  const cfg_infot &cfg_info)
{
  if(can_cast_expr<symbol_exprt>(lhs))
  {
    const auto &symbol_expr = to_symbol_expr(lhs);
    const auto &id = symbol_expr.get_identifier();

    check_source_location.set_comment(
      "Check that " + from_expr_using_mode(ns, language_mode, lhs) +
      " is assignable");

    if(cfg_info.is_local(id))
      return false;

    // this is a global symbol. Ignore if it is one of the CPROVER globals
    if(is_cprover_symbol(id))
    {
      check_source_location.set_comment(
        "Check that " + from_expr_using_mode(ns, language_mode, lhs) +
        " is assignable");

      return false;
    }

    return true;
  }
  else
  {
    // This is a more complex expression.
    // Since non-dirty locals are not tracked explicitly in the write set,
    // we need to skip the check if we can verify that the expression describes
    // an access to a non-dirty local symbol or an function parameter,
    // otherwise the check will necessarily fail.
    // If the expression contains address_of operator,
    // the assignment gets checked. If the base object of the expression
    // is a local or a function parameter, it will also be flagged as dirty and
    // will be tracked explicitly, and the check will pass.
    // If the expression contains a dereference operation, the assignment gets
    // checked. If the dereferenced address was computed from a local object,
    // from a function parameter or returned by a local malloc,
    // then the object will also be tracked explicitly for being dirty,
    // and the check will pass.
    // In all other cases (address of a non-local object, or dereference of
    // a non-locally computed address) the location must be given explicitly
    // in the assigns clause to be allowed for assignment  and we must check
    // the assignment.
    if(cfg_info.is_local_composite_access(lhs))
    {
      check_source_location.set_comment(
        "Check that " + from_expr_using_mode(ns, language_mode, lhs) +
        " is assignable");

      return false;
    }

    return true;
  }
}

void dfcc_instrumentt::instrument_lhs(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  const exprt &lhs,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  const auto &mode = utils.get_function_symbol(function_id).mode;

  goto_programt payload;

  const auto &lhs_source_location = target->source_location();
  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), lhs_source_location));

  source_locationt check_source_location(target->source_location());
  check_source_location.set_property_class("assigns");
  check_source_location.set_comment(
    "Check that " + from_expr_using_mode(ns, mode, lhs) + " is assignable");

  if(must_check_lhs(
       target->source_location(), check_source_location, mode, lhs, cfg_info))
  {
    // ```
    // IF !write_set GOTO skip_target;
    // DECL check_assign: bool;
    // CALL check_assign = check_assignment(write_set, &lhs, sizeof(lhs));
    // ASSERT(check_assign);
    // DEAD check_assign;
    // skip_target: SKIP;
    // ----
    // ASSIGN lhs := rhs;
    // ```

    auto &check_sym = utils.create_symbol(
      bool_typet(),
      id2string(function_id),
      "__check_lhs_assignment",
      lhs_source_location,
      mode,
      utils.get_function_symbol(function_id).module,
      false);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var, lhs_source_location));

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var,
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_ASSIGNMENT]
          .symbol_expr(),
        {write_set,
         typecast_exprt::conditional_cast(
           address_of_exprt(lhs), pointer_type(empty_typet{})),
         utils.make_sizeof_expr(lhs)}},
      lhs_source_location));

    payload.add(
      goto_programt::make_assertion(check_var, check_source_location));
    payload.add(goto_programt::make_dead(check_var));
  }
  else
  {
    // ```
    // IF !write_set GOTO skip_target;
    // ASSERT(true);
    // skip_target: SKIP;
    // ----
    // ASSIGN lhs := rhs;
    // ```
    payload.add(
      goto_programt::make_assertion(true_exprt(), check_source_location));
  }

  auto label_instruction =
    payload.add(goto_programt::make_skip(lhs_source_location));
  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
}

/// Checks if lhs is the `dead_object`, and if the rhs
/// is an `if_exprt(nondet, ptr, dead_object)` expression.
/// Returns `ptr` if the pattern was matched, nullptr otherwise.
optionalt<exprt>
dfcc_instrumentt::is_dead_object_update(const exprt &lhs, const exprt &rhs)
{
  if(
    lhs.id() == ID_symbol &&
    to_symbol_expr(lhs).get_identifier() == CPROVER_PREFIX "dead_object")
  {
    // error out if rhs is different from `if_exprt(nondet, ptr, dead_object)`
    PRECONDITION(rhs.id() == ID_if);
    auto &if_expr = to_if_expr(rhs);
    PRECONDITION(can_cast_expr<side_effect_expr_nondett>(if_expr.cond()));
    PRECONDITION(if_expr.false_case() == lhs);
    return if_expr.true_case();
  }
  else
  {
    return {};
  }
}

void dfcc_instrumentt::instrument_assign(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  const auto &lhs = target->assign_lhs();
  const auto &rhs = target->assign_rhs();
  const auto &target_location = target->source_location();

  // check the lhs
  instrument_lhs(function_id, write_set, target, lhs, goto_program, cfg_info);

  // handle dead_object updates (created by __builtin_alloca for instance)
  // Remark: we do not really need to track this deallocation since the default
  // CBMC checks are already able to detect writes to DEAD objects
  const auto dead_ptr = is_dead_object_update(lhs, rhs);
  if(dead_ptr.has_value())
  {
    // ```
    // ASSIGN dead_object := if_exprt(nondet, ptr, dead_object);
    // ----
    // IF !write_set GOTO skip_target;
    // CALL record_deallocated(write_set, ptr);
    // skip_target: SKIP;
    // ```

    // step over the instruction
    target++;

    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set), target_location));

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RECORD_DEALLOCATED]
          .symbol_expr(),
        {write_set, dead_ptr.value()}},
      target_location));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);

    // step back
    target--;
  }

  // is the rhs expression a side_effect("allocate") expression ?
  if(rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_allocate)
  {
    // ```
    // CALL lhs := side_effect(statemet = ID_allocate, args = {size, clear});
    // ----
    // IF !write_set GOTO skip_target;
    // CALL add_allocated(write_set, lhs);
    // skip_target: SKIP;
    // ```

    // step over the instruction
    target++;

    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set), target_location));

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_ADD_ALLOCATED]
          .symbol_expr(),
        {write_set, lhs}},
      target_location));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);

    // step back
    target--;
  }
}

void dfcc_instrumentt::instrument_fptr_call_instruction_dynamic_lookup(
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program)
{
  // Insert a dynamic lookup in __instrumented_functions_map
  // and pass the write set only to functions that are known to be able
  // to accept it.
  //
  // ```
  // IF __instrumented_functions_map[__CPROVER_POINTER_OBJECT(fptr)] != 1
  //   GOTO no_inst;
  // CALL [lhs] = fptr(params, write_set);
  // GOTO end;
  // no_inst:
  // CALL [lhs] = fptr(params);
  // end:
  // SKIP;
  // ---
  // SKIP // [lhs] = fptr(params) turned into SKIP
  // ```
  const auto &target_location = target->source_location();
  const auto &callf = target->call_function();
  auto object_id = pointer_object(
    (callf.id() == ID_dereference) ? to_dereference_expr(callf).pointer()
                                   : address_of_exprt(callf));
  auto index_expr = index_exprt(
    library.get_instrumented_functions_map_symbol().symbol_expr(), object_id);
  auto cond = notequal_exprt(index_expr, from_integer(1, unsigned_char_type()));
  goto_programt payload;
  auto goto_no_inst =
    payload.add(goto_programt::make_incomplete_goto(cond, target_location));
  code_function_callt call_inst(
    target->call_lhs(), target->call_function(), target->call_arguments());
  call_inst.arguments().push_back(write_set);
  payload.add(goto_programt::make_function_call(call_inst, target_location));
  auto goto_end_inst = payload.add(
    goto_programt::make_incomplete_goto(true_exprt(), target_location));
  auto no_inst_label = payload.add(goto_programt::make_skip(target_location));
  goto_no_inst->complete_goto(no_inst_label);
  code_function_callt call_no_inst(
    target->call_lhs(), target->call_function(), target->call_arguments());
  payload.add(goto_programt::make_function_call(call_no_inst, target_location));
  auto end_label = payload.add(goto_programt::make_skip(target_location));
  goto_end_inst->complete_goto(end_label);
  // erase the original call
  target->turn_into_skip();
  insert_before_swap_and_advance(goto_program, target, payload);
}

void dfcc_instrumentt::instrument_call_instruction(
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program)
{
  if(target->is_function_call())
  {
    if(target->call_function().id() == ID_symbol)
    {
      // this is a function call
      if(!do_not_instrument(
           to_symbol_expr(target->call_function()).get_identifier()))
      {
        // pass write set argument only if function is known to be instrumented
        target->call_arguments().push_back(write_set);
      }
    }
    else
    {
      // This is a function pointer call. We insert a dynamic lookup into the
      // map of instrumented functions to determine if the target function is
      // able to accept a write set parameter.
      instrument_fptr_call_instruction_dynamic_lookup(
        write_set, target, goto_program);
    }
  }
}

void dfcc_instrumentt::instrument_deallocate_call(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program)
{
  INVARIANT(target->is_function_call(), "target must be a function call");
  INVARIANT(
    target->call_function().id() == ID_symbol &&
      (id2string(to_symbol_expr(target->call_function()).get_identifier()) ==
       CPROVER_PREFIX "deallocate"),
    "target must be a call to" CPROVER_PREFIX "deallocate");

  auto &target_location = target->source_location();
  // ```
  // IF !write_set GOTO skip_target;
  // DECL check_deallocate: bool;
  // CALL check_deallocate := check_deallocate(write_set, ptr);
  // ASSERT(check_deallocate);
  // DEAD check_deallocate;
  // CALL record_deallocated(write_set, lhs);
  // skip_target: SKIP;
  // ----
  // CALL __CPROVER_deallocate(ptr);
  // ```
  const auto &mode = utils.get_function_symbol(function_id).mode;
  goto_programt payload;

  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), target_location));

  auto &check_sym = get_fresh_aux_symbol(
    bool_typet(),
    id2string(function_id),
    "__check_deallocate",
    target_location,
    mode,
    goto_model.symbol_table);

  const auto &check_var = check_sym.symbol_expr();

  payload.add(goto_programt::make_decl(check_var, target_location));

  const auto &ptr = target->call_arguments().at(0);

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      check_var,
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_DEALLOCATE]
        .symbol_expr(),
      {write_set, ptr}},
    target_location));

  // add property class on assertion source_location
  source_locationt check_location(target_location);
  check_location.set_property_class("frees");
  std::string comment =
    "Check that " + from_expr_using_mode(ns, mode, ptr) + " is freeable";
  check_location.set_comment(comment);

  payload.add(goto_programt::make_assertion(check_var, check_location));
  payload.add(goto_programt::make_dead(check_var, target_location));

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RECORD_DEALLOCATED]
        .symbol_expr(),
      {write_set, ptr}},
    target_location));

  auto label_instruction =
    payload.add(goto_programt::make_skip(target_location));
  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
}

void dfcc_instrumentt::instrument_function_call(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  INVARIANT(
    target->is_function_call(),
    "the target must be a function call instruction");

  // Instrument the lhs if any.
  if(target->call_lhs().is_not_nil())
  {
    instrument_lhs(
      function_id,
      write_set,
      target,
      target->call_lhs(),
      goto_program,
      cfg_info);
  }

  const auto &call_function = target->call_function();
  if(
    call_function.id() == ID_symbol &&
    (id2string(to_symbol_expr(call_function).get_identifier()) == CPROVER_PREFIX
     "deallocate"))
  {
    instrument_deallocate_call(function_id, write_set, target, goto_program);
  }
  else
  {
    // instrument as a normal function/function pointer call
    instrument_call_instruction(write_set, target, goto_program);
  }
}

void dfcc_instrumentt::instrument_other(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  const auto &target_location = target->source_location();
  auto &statement = target->get_other().get_statement();

  if(statement == ID_array_set || statement == ID_array_copy)
  {
    const bool is_array_set = statement == ID_array_set;
    // ```
    // IF !write_set GOTO skip_target;
    // DECL check_array_set: bool;
    // CALL check_array_set = check_array_set(write_set, dest);
    // ASSERT(check_array_set);
    // DEAD check_array_set;
    // skip_target: SKIP;
    // ----
    // OTHER {statemet = array_set, args = {dest, value}};
    // ```
    const auto &mode = utils.get_function_symbol(function_id).mode;
    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set), target_location));

    auto &check_sym = get_fresh_aux_symbol(
      bool_typet(),
      id2string(function_id),
      is_array_set ? "__check_array_set" : "__check_array_copy",
      target_location,
      mode,
      goto_model.symbol_table);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var, target_location));

    const auto &dest = target->get_other().operands().at(0);

    symbolt &check_fun =
      library.dfcc_fun_symbol
        [is_array_set ? dfcc_funt::WRITE_SET_CHECK_ARRAY_SET
                      : dfcc_funt::WRITE_SET_CHECK_ARRAY_COPY];
    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var, check_fun.symbol_expr(), {write_set, dest}},
      target_location));

    // add property class on assertion source_location
    source_locationt check_location(target_location);
    check_location.set_property_class("assigns");

    std::string fun_name = is_array_set ? "array_set" : "array_copy";

    std::string comment = "Check that " + fun_name + "(" +
                          from_expr_using_mode(ns, mode, dest) +
                          ", ...) is allowed by the assigns clause";
    check_location.set_comment(comment);

    payload.add(goto_programt::make_assertion(check_var, check_location));
    payload.add(goto_programt::make_dead(check_var));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);
  }
  else if(statement == ID_array_replace)
  {
    // ```
    // IF !write_set GOTO skip_target;
    // DECL check_array_replace: bool;
    // CALL check_array_replace = check_array_replace(write_set, dest);
    // ASSERT(check_array_replace);
    // DEAD check_array_replace;
    // skip_target: SKIP;
    // ----
    // OTHER {statemet = array_replace, args = {dest, src}};
    // ```
    const auto &mode = utils.get_function_symbol(function_id).mode;
    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set)));

    auto &check_sym = get_fresh_aux_symbol(
      bool_typet(),
      id2string(function_id),
      "__check_array_replace",
      target_location,
      mode,
      goto_model.symbol_table);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var));

    const auto &dest = target->get_other().operands().at(0);
    const auto &src = target->get_other().operands().at(1);

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var,
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_ARRAY_REPLACE]
          .symbol_expr(),
        {write_set, dest, src}},
      target_location));

    // add property class on assertion source_location
    source_locationt check_location(target_location);
    check_location.set_property_class("assigns");
    std::string comment = "Check that array_replace(" +
                          from_expr_using_mode(ns, mode, dest) +
                          ", ...) is allowed by the assigns clause";
    check_location.set_comment(comment);

    payload.add(goto_programt::make_assertion(check_var, check_location));
    payload.add(goto_programt::make_dead(check_var, target_location));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);
  }
  else if(statement == ID_havoc_object)
  {
    // insert before instruction
    // ```
    // IF !write_set GOTO skip_target;
    // DECL check_havoc_object: bool;
    // CALL check_havoc_object = check_havoc_object(write_set, ptr);
    // ASSERT(check_havoc_object);
    // DEAD check_havoc_object;
    // ```
    const auto &mode = utils.get_function_symbol(function_id).mode;
    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set), target_location));

    auto &check_sym = get_fresh_aux_symbol(
      bool_typet(),
      id2string(function_id),
      "__check_havoc_object",
      target_location,
      mode,
      goto_model.symbol_table);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var));

    const auto &ptr = target->get_other().operands().at(0);

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var,
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_HAVOC_OBJECT]
          .symbol_expr(),
        {write_set, ptr}},
      target_location));

    // add property class on assertion source_location
    source_locationt check_location(target_location);
    check_location.set_property_class("assigns");
    std::string comment = "Check that havoc_object(" +
                          from_expr_using_mode(ns, mode, ptr) +
                          ") is allowed by the assigns clause";
    check_location.set_comment(comment);

    payload.add(goto_programt::make_assertion(check_var, check_location));
    payload.add(goto_programt::make_dead(check_var, target_location));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);
  }
  else if(statement == ID_expression)
  {
    // When in Rome do like the Romans (cf src/pointer_analysis/value_set.cpp)
    // can be ignored, we don't expect side effects here
  }
  else
  {
    // Other cases not presently handled
    // * ID_array_equal
    // * ID_decl         track new symbol ?
    // * ID_cpp_delete
    // * ID_printf       track as side effect on stdout ?
    // * code_inputt     track as nondet ?
    // * code_outputt    track as side effect on stdout ?
    // * ID_nondet       track as nondet ?
    // * ID_asm          track as side effect depending on the instruction ?
    // * ID_user_specified_predicate
    //                   should be pure ?
    // * ID_user_specified_parameter_predicates
    //                   should be pure ?
    // * ID_user_specified_return_predicates
    //                   should be pure ?
    // * ID_fence
    //                   bail out ?
    log.warning().source_location = target_location;
    log.warning() << "dfcc_instrument::instrument_other: statement type '"
                  << statement << "' is not supported, analysis may be unsound"
                  << messaget::eom;
  }
}
