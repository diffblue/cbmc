/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Translate functions that specify assignable and freeable targets
/// declaratively into active functions that build write sets dynamically
/// by rewriting calls to front-end functions into calls to library functions
/// defining their dynamic semantics.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_SPEC_FUNCTIONS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_SPEC_FUNCTIONS_H

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "dfcc_library.h"
#include "dfcc_utils.h"

#include <map>
#include <set>

class goto_modelt;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;

/// This class rewrites GOTO functions that use the built-ins:
/// - `__CPROVER_assignable`,
/// - `__CPROVER_object_whole`,
/// - `__CRPOVER_object_from`,
/// - `__CPROVER_object_upto`,
/// - `__CPROVER_freeable`
/// into GOTO functions that populate a write set instance or havoc a write set
/// by calling the library implementation of these built-ins.
class dfcc_spec_functionst
{
public:
  dfcc_spec_functionst(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library);

  /// From a function:
  ///
  /// ```
  /// void function_id(params);
  /// ```
  ///
  /// generates a new function:
  ///
  /// ```
  /// void havoc_function_id(__CPROVER_assignable_set_ptr_t write_set_to_havoc);
  /// ```
  ///
  /// Which havocs the targets specified by `function_id`, passed
  ///
  /// \param function_id function to generate instructions from
  /// \param havoc_function_id write set variable to havoc
  /// \param nof_targets maximum number of targets to havoc
  ///
  void generate_havoc_function(
    const irep_idt &function_id,
    const irep_idt &havoc_function_id,
    std::size_t &nof_targets);

  /// Translates \p original_program that specifies assignable targets
  /// into a program that havocs the targets.
  ///
  /// \pre The \p original_program must be already fully inlined, and the only
  /// function calls allowed are to the built-ins that specify
  /// assignable targets: `__CPROVER_assignable`, `__CPROVER_object_whole`,
  /// `__CPROVER_object_from`, `__CPROVER_object_upto`.
  ///
  /// \details The \p original_program is assumed to encode an assigns clause
  /// using the built-ins `__CPROVER_assignable`, `__CPROVER_object_whole`,
  /// `__CPROVER_object_from`, `__CPROVER_object_upto`.
  /// The method traverses \p original_program and emits a sequence of GOTO
  /// instructions in \p havoc_program that encode the havocing of the target
  /// write set \p write_set_to_havoc.
  ///
  /// \param[in] function_id function id to use for prefixing fresh variables
  /// \param[in] mode function id to use for prefixing fresh variables
  /// \param[in] module function id to use for prefixing fresh variables
  /// \param[in] original_program program from which to derive the havoc program
  /// \param[in] write_set_to_havoc write set symbol to havoc
  /// \param[out] havoc_program destination program for havoc instructions
  /// \param[out] nof_targets max number of havoc targets discovered
  ///
  void generate_havoc_instructions(
    const irep_idt &function_id,
    const irep_idt &mode,
    const irep_idt &module,
    const goto_programt &original_program,
    const exprt &write_set_to_havoc,
    goto_programt &havoc_program,
    std::size_t &nof_targets);

  /// Transforms (in place) a function
  ///
  /// ```
  /// void function_id(params);
  /// ```
  ///
  /// into a function
  ///
  /// ```
  /// void function_id(
  ///   params,
  ///   __CPROVER_assignable_set_t write_set_to_fill,
  /// )
  /// ```
  ///
  /// Where:
  /// - `write_set_to_fill` is the write set to populate.
  ///
  /// \param function_id function to transform in place
  /// \param nof_targets receives the estimated size of the write set
  ///
  void to_spec_assigns_function(
    const irep_idt &function_id,
    std::size_t &nof_targets);

  /// Rewrites in place \p program expressed in terms of built-ins specifying
  /// assignable targets declaratively using `__CPROVER_assignable`,
  /// `__CPROVER_object_whole`, `__CPROVER_object_from`,
  /// `__CPROVER_object_upto` into a program populating \p write_set_to_fill.
  ///
  /// It is the responsibility of the caller of this method to instrument the
  /// resulting program against another write set instance to check them for
  /// unwanted side effects.
  ///
  /// \pre The \p program must be already fully inlined, and the only
  /// function calls allowed are to the built-ins that specify
  /// assignable targets: `__CPROVER_assignable`, `__CPROVER_object_whole`,
  /// `__CPROVER_object_from`, `__CPROVER_object_upto`.
  ///
  /// \param[in] write_set_to_fill write set to populate.
  /// \param[in] language_mode used to format expressions.
  /// \param[inout] program function to transform in place
  /// \param[out] nof_targets receives the estimated size of the write set
  ///
  void to_spec_assigns_instructions(
    const exprt &write_set_to_fill,
    const irep_idt &language_mode,
    goto_programt &program,
    std::size_t &nof_targets);

  /// Transforms (in place) a function
  ///
  /// ```
  /// void function_id(params);
  /// ```
  ///
  /// into a function
  ///
  /// ```
  /// void function_id(
  ///   params,
  ///   __CPROVER_assignable_set_t write_set_to_fill,
  /// )
  /// ```
  ///
  /// Where:
  /// - `write_set_to_fill` is the write set to populate.
  ///
  /// The function must be fully inlined and loop free.
  ///
  /// \param function_id function to transform in place
  /// \param nof_targets receives the estimated size of the write set
  ///
  void
  to_spec_frees_function(const irep_idt &function_id, std::size_t &nof_targets);

  /// Rewrites in place \p program expressed in terms of built-ins specifying
  /// freeable targets declaratively using `__CPROVER_freeable` into a program
  /// populating \p write_set_to_fill.
  ///
  /// It is the responsibility of the caller of this method to instrument the
  /// resulting program against another write set instance to check them for
  /// unwanted side effects.
  ///
  /// \pre The \p program must be already fully inlined, and the only
  /// function calls allowed are to the built-ins that specify
  /// freeable targets: `__CPROVER_freeable`.
  ///
  /// \param[in] write_set_to_fill write set to populate.
  /// \param[in] language_mode used to format expressions.
  /// \param[inout] program function to transform in place
  /// \param[out] nof_targets receives the estimated size of the write set
  ///
  void to_spec_frees_instructions(
    const exprt &write_set_to_fill,
    const irep_idt &language_mode,
    goto_programt &program,
    std::size_t &nof_targets);

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  namespacet ns;

  /// Extracts the type of an assigns clause target expression
  /// The expression must be of the form:
  /// `expr = cast(address_of(target), empty*)`
  const typet &get_target_type(const exprt &expr);
};

#endif
