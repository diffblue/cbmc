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
#include <util/suffix.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <ansi-c/c_expr.h>
#include <goto-instrument/contracts/cfg_info.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_is_freeable.h"
#include "dfcc_is_fresh.h"
#include "dfcc_library.h"
#include "dfcc_utils.h"

std::set<irep_idt> dfcc_instrumentt::function_cache;

dfcc_instrumentt::dfcc_instrumentt(
  goto_modelt &goto_model,
  messaget &log,
  dfcc_utilst &utils,
  dfcc_libraryt &library)
  : goto_model(goto_model),
    log(log),
    message_handler(log.get_message_handler()),
    utils(utils),
    library(library),
    ns(goto_model.symbol_table)
{
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

// these are internal symbols which implementation is generated and inlined into
// the model at conversion or symex time and must not be instrumented
static std::set<irep_idt> internal_symbol = {
  // these are come from different assert.h implementation on different systems
  // and eventually become ASSERT instructions and must not be instrumented
  "__assert_fail",
  "_assert",
  "__assert_c99",
  "_wassert",
  "__assert_rtn",
  "__assert",
  "__assert_func",

  /// These builtins are translated to no-ops and must not be instrumented
  "__builtin_prefetch",
  "__builtin_unreachable",

  /// These builtins are valist management functions
  /// and interpreted natively in src/goto-symex/symex_builtin_functions.cpp
  /// and must not be instrumented
  ID_gcc_builtin_va_arg,
  "__builtin_va_copy",
  "__builtin_va_start",
  "__va_start",
  "__builtin_va_end",

  /// These builtins get translated to CPROVER equivalents
  /// and must not be instrumented
  "__builtin_isgreater",
  "__builtin_isgreaterequal",
  "__builtin_isless",
  "__builtin_islessequal",
  "__builtin_islessgreater",
  "__builtin_isunordered",
};

/// True iff the symbol must not be instrumented
bool dfcc_instrumentt::is_internal_symbol(const irep_idt &id) const
{
  // TODO could <goto-programs/system_library_symbols.h> be used instead ?
  return internal_symbol.find(id) != internal_symbol.end();
}

/// True iff `id` starts with `prefix`
inline bool has_prefix(const irep_idt &id, std::string prefix)
{
  return id2string(id).rfind(prefix, 0) == 0;
}

/// True if id has `CPROVER_PREFIX` or `__VERIFIER` or `nondet` prefix,
/// or an `&object` suffix (cf system_library_symbols.cpp)
bool dfcc_instrumentt::is_cprover_symbol(const irep_idt &id) const
{
  return has_prefix(id, CPROVER_PREFIX) || has_prefix(id, "__VERIFIER") ||
         has_prefix(id, "nondet") || has_suffix(id2string(id), "$object");
}

bool dfcc_instrumentt::do_not_instrument(const irep_idt &id) const
{
  return !has_prefix(id, CPROVER_PREFIX "file_local") &&
         (is_cprover_symbol(id) || is_internal_symbol(id));
}

void dfcc_instrumentt::instrument_harness_function(const irep_idt &function_id)
{
  log.debug() << "->dfcc_instrumentt::instrument_harness_function("
              << function_id << ")" << messaget::eom;
  if(
    dfcc_instrumentt::function_cache.find(function_id) !=
    dfcc_instrumentt::function_cache.end())
    return;

  dfcc_instrumentt::function_cache.insert(function_id);

  const auto null_expr = null_pointer_exprt(
    to_pointer_type(library.dfcc_type[dfcc_typet::WRITE_SET_PTR]));

  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);
  auto &body = goto_function.body;

  // rewrite is_fresh_calls
  dfcc_is_fresht is_fresh(library, log);
  is_fresh.rewrite_calls(body, null_expr);

  // rewrite is_freeable/is_freed calls
  dfcc_is_freeablet is_freeable(library, log);
  is_freeable.rewrite_calls(body, null_expr);

  // rewrite calls
  Forall_goto_program_instructions(it, body)
  {
    if(it->is_function_call())
      instrument_call_instruction(null_expr, it, body);
  }

  goto_model.goto_functions.update();

  // debug print
  forall_goto_program_instructions(it, body)
  {
    body.output_instruction(ns, function_id, log.debug(), *it);
  }
  log.debug() << "<-dfcc_instrumentt::instrument_harness_function("
              << function_id << ")" << messaget::eom;
}

void dfcc_instrumentt::instrument_function(const irep_idt &function_id)
{
  log.debug() << "->dfcc_instrumentt::instrument_function(" << function_id
              << ")" << messaget::eom;

  // never instrument a function twice
  if(
    dfcc_instrumentt::function_cache.find(function_id) !=
    dfcc_instrumentt::function_cache.end())
    return;

  dfcc_instrumentt::function_cache.insert(function_id);

  auto found = goto_model.goto_functions.function_map.find(function_id);
  if(found == goto_model.goto_functions.function_map.end())
  {
    // abort on missing functions since if they ever get called/used
    // they would not be transformed/available and unsound
    log.error() << "dfcct::transform_goto_model: function '" << function_id
                << "' was not found in the function map." << messaget::eom;
    throw 0;
    // TODO create an entry in the function table
    // if the function is not in the list of functions expected
    // not to have a body then create body with assert(false)assume(false)
  }
  else
  {
    auto &goto_function = found->second;

    function_cfg_infot cfg_info(goto_function);

    const auto &write_set = utils.add_parameter(
      function_id,
      "__write_set_to_check",
      library.dfcc_type[dfcc_typet::WRITE_SET_PTR]);

    instrument_function_body(function_id, write_set.symbol_expr(), cfg_info);
    log.debug() << "->dfcc_instrumentt::instrument_function(" << function_id
                << ")" << messaget::eom;
  }
}

void dfcc_instrumentt::instrument_function_body(
  const irep_idt &function_id,
  const exprt &write_set,
  cfg_infot &cfg_info)
{
  log.debug() << "<-dfcc_instrumentt::instrument_function_body(" << function_id
              << ")" << messaget::eom;

  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  if(!goto_function.body_available())
  {
    log.warning() << "dfcc_instrumentt::instrument_function: '" << function_id
                  << "' body is unavailable. Results may be unsound if the real"
                     "function happens to have side effects."
                  << messaget::eom;
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
    {});

  // cleanup
  remove_skip(body);

  // recalculate numbers, etc.
  goto_model.goto_functions.update();

  // add loop ids
  goto_model.goto_functions.compute_loop_numbers();

  // debug print instrumented body
  forall_goto_program_instructions(ins_it, goto_function.body)
  {
    goto_function.body.output_instruction(
      ns, function_id, log.debug(), *ins_it);
  }
  log.debug() << "<-dfcc_instrumentt::instrument_function_body(" << function_id
              << ")" << messaget::eom;
}

void dfcc_instrumentt::instrument_goto_program(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const exprt &write_set)
{
  log.debug() << "->dfcc_instrumentt::instrument_goto_program(" << function_id
              << ")" << messaget::eom;

  goto_program_cfg_infot cfg_info(goto_program);

  instrument_instructions(
    function_id,
    write_set,
    goto_program,
    goto_program.instructions.begin(),
    goto_program.instructions.end(),
    cfg_info,
    // no pred, don't skip any instructions
    {});

  // cleanup
  remove_skip(goto_program);

  // debug print
  forall_goto_program_instructions(ins_it, goto_program)
  {
    goto_program.output_instruction(ns, function_id, log.debug(), *ins_it);
  }
  log.debug() << "<-dfcc_instrumentt::instrument_goto_program(" << function_id
              << ")" << messaget::eom;
}

void dfcc_instrumentt::instrument_instructions(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt &goto_program,
  goto_programt::targett first_instruction,
  const goto_programt::targett &last_instruction,
  cfg_infot &cfg_info,
  const std::function<bool(const goto_programt::targett &)> &pred)
{
  log.debug() << "->dfcc_instrumentt::instrument_instructions(" << function_id
              << ")" << messaget::eom;

  // rewrite is_fresh calls
  dfcc_is_fresht is_fresh(library, log);
  is_fresh.rewrite_calls(
    goto_program, first_instruction, last_instruction, write_set);

  // rewrite is_freeable/is_freed calls
  dfcc_is_freeablet is_freeable(library, log);
  is_freeable.rewrite_calls(
    goto_program, first_instruction, last_instruction, write_set);

  const auto ns = namespacet(goto_model.symbol_table);
  auto &target = first_instruction;

  // excluding the last
  while(target != last_instruction)
  {
    // Skip instructions marked as disabled for assigns clause checking
    // or rejected by the predicate
    if((pred && !pred(target)))
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
#if 0
      // Remark: we do not really need to record DEAD instructions since the
      // default CBMC checks are already able to detect writes to DEAD objects
      instrument_dead(function_id, write_set, target, goto_program, cfg_info);
#endif
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
  log.debug() << "<-dfcc_instrumentt::instrument_instructions(" << function_id
              << ")" << messaget::eom;
}

bool dfcc_instrumentt::must_track_decl_or_dead(
  const goto_programt::targett &target,
  const cfg_infot &cfg_info) const
{
  INVARIANT(
    target->is_decl() || target->is_dead(),
    "dfcc_instrumentt::must_track_decl_or_dead: target must be a DECL or DEAD "
    "instruction");

  const auto &ident = target->is_decl()
                        ? target->decl_symbol().get_identifier()
                        : target->dead_symbol().get_identifier();
  bool retval = cfg_info.is_not_local_or_dirty_local(ident);

  log.debug() << "dfcc_instrumentt::must_track_decl_or_dead(" << ident
              << ") is_not_local_or_dirty_local = " << retval << messaget::eom;
  return retval;
}

void dfcc_instrumentt::instrument_decl(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  if(!must_track_decl_or_dead(target, cfg_info))
    return;

  // ```
  // DECL x;
  // ----
  // IF !write_set GOTO skip_target;
  // CALL add_allocated(write_set, &x);
  // skip_target: SKIP;
  // ```
  const auto &decl_symbol = target->decl_symbol();
  // step over instruction
  target++;
  goto_programt payload;
  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), target->source_location()));

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_ADD_ALLOCATED].symbol_expr(),
      {write_set, address_of_exprt(decl_symbol)}},
    target->source_location()));

  auto label_instruction =
    payload.add(goto_programt::make_skip(target->source_location()));
  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
  // step back
  target--;
}

void dfcc_instrumentt::instrument_dead(
  const irep_idt &function_id,
  const exprt &write_set,
  goto_programt::targett &target,
  goto_programt &goto_program,
  cfg_infot &cfg_info)
{
  if(!must_track_decl_or_dead(target, cfg_info))
    return;

  // ```
  // IF !write_set GOTO skip_target;
  // CALL record_dead(write_set, &x);
  // skip_target: SKIP;
  // ----
  // DEAD x;
  // ```
  const auto &decl_symbol = target->dead_symbol();

  goto_programt payload;

  auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
    utils.make_null_check_expr(write_set), target->source_location()));

  payload.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RECORD_DEAD].symbol_expr(),
      {write_set, address_of_exprt(decl_symbol)}},
    target->source_location()));

  auto label_instruction =
    payload.add(goto_programt::make_skip(target->source_location()));

  goto_instruction->complete_goto(label_instruction);

  insert_before_swap_and_advance(goto_program, target, payload);
}

/// Returns true iff the lhs of a `ASSIGN lhs := ...` instruction or
/// `CALL lhs := ...` must be checked against the write set.
bool dfcc_instrumentt::must_check_lhs(
  const source_locationt &lhs_source_location,
  source_locationt &check_source_location,
  const irep_idt &language_mode,
  const exprt &lhs,
  const cfg_infot &cfg_info)
{
  log.debug().source_location = lhs_source_location;

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

      log.debug()
        << "dfcc_instrumentt: Assignment to local symbol composite member "
        << format(lhs) << messaget::eom;
      return false;
    }

    log.debug() << "dfcc_instrumentt: checking assignment to expression "
                << format(lhs) << messaget::eom;
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

    auto &check_sym = get_fresh_aux_symbol( // TODO use dfcc_utilst class
      bool_typet(),
      id2string(function_id),
      "__check_lhs_assignment",
      lhs_source_location,
      mode,
      goto_model.symbol_table);

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

    // TODO add property class on assertion source_location
    std::string comment =
      "Check that " + from_expr_using_mode(ns, mode, lhs) + " is assignable";
    check_source_location.set_comment(comment);
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
const exprt *
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
    return &if_expr.true_case();
  }
  else
  {
    return nullptr;
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
#if 0
  const auto &dead_ptr = is_dead_object_update(lhs, rhs);
  if(dead_ptr != nullptr)
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
        {write_set, *dead_ptr}},
      target_location));

    auto label_instruction =
      payload.add(goto_programt::make_skip(target_location));
    goto_instruction->complete_goto(label_instruction);

    insert_before_swap_and_advance(goto_program, target, payload);

    // step back
    target--;
  }
#endif

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
  auto cond = notequal_exprt(index_expr, from_integer(1, c_bool_typet(8)));
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
      if(do_not_instrument(
           to_symbol_expr(target->call_function()).get_identifier()))
      {
        // do not pass write set if we know the function is not instrumented
        return;
      }
      // pass write set argument
      target->call_arguments().push_back(write_set);
    }
    else
    {
      // this is a function pointer call.
      // pass write set argument
      target->call_arguments().push_back(write_set);
      // TODO use instrument_fptr_call_instruction_dynamic_lookup once symex
      // is able to dispatch function pointers internally
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
  log.debug() << "instrument_function_call" << messaget::eom;

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
  if(statement == ID_array_set)
  {
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
      "__check_array_set",
      target_location,
      mode,
      goto_model.symbol_table);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var, target_location));

    const auto &dest = target->get_other().operands().at(0);

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var,
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_ARRAY_SET]
          .symbol_expr(),
        {write_set, dest}},
      target_location));

    // add property class on assertion source_location
    source_locationt check_location(target_location);
    check_location.set_property_class("assigns");
    std::string comment = "Check that array_set(" +
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
  else if(statement == ID_array_copy)
  {
    // ```
    // IF !write_set GOTO skip_target;
    // DECL check_array_copy: bool;
    // CALL check_array_copy = check_array_copy(write_set, dest);
    // ASSERT(check_array_copy);
    // DEAD check_array_copy;
    // skip_target: SKIP;
    // ----
    // OTHER {statemet = array_copy, args = {dest, src}};
    // ```
    const auto &mode = utils.get_function_symbol(function_id).mode;
    goto_programt payload;

    auto goto_instruction = payload.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(write_set)));

    auto &check_sym = get_fresh_aux_symbol(
      bool_typet(),
      id2string(function_id),
      "__check_array_copy",
      target_location,
      mode,
      goto_model.symbol_table);

    const auto &check_var = check_sym.symbol_expr();

    payload.add(goto_programt::make_decl(check_var));

    const auto &dest = target->get_other().operands().at(0);

    payload.add(goto_programt::make_function_call(
      code_function_callt{
        check_var,
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_ARRAY_COPY]
          .symbol_expr(),
        {write_set, dest}},
      target_location));

    // add property class on assertion source_location
    source_locationt check_location(target_location);
    check_location.set_property_class("assigns");
    std::string comment = "Check that array_copy(" +
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
