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

#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_utils.h"

#include <map>
#include <set>

class goto_modelt;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;
class cfg_infot;

/// This class transforms (in place) declarative assigns clause and frees clause
/// specification functions expressed in terms of the builtins:
/// - `__CPROVER_assignable`,
/// - `__CPROVER_object_whole`,
/// - `__CRPOVER_object_from`,
/// - `__CPROVER_object_upto`,
/// - `__CPROVER_freeable`
/// into active functions by transforming the builtin calls into calls to
/// dfcc library functions that actually built frame descriptions.
/// The resulting function is then itself instrumented for frame condition
/// checking to be able to prove the absence of side effects.
class dfcc_spec_functionst
{
public:
  dfcc_spec_functionst(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument);

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
  ///   __CPROVER_assignable_set_t write_set_to_check
  /// )
  /// ```
  ///
  /// Where:
  /// - `write_set_to_fill` is the write set to populate.
  /// - `write_set_to_check` is the write set to use for checking side effects.
  ///
  /// \param function_id function to transform in place
  /// \param nof_targets receives the estimated size of the write set
  ///
  void to_spec_assigns_function(
    const irep_idt &function_id,
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
  ///   __CPROVER_assignable_set_t write_set_to_check
  /// )
  /// ```
  ///
  /// Where:
  /// - `write_set_to_fill` is the write set to populate.
  /// - `write_set_to_check` is the write set to use for checking side effects.
  ///
  /// The function must be fully inlined and loop free.
  ///
  /// \param function_id function to transform in place
  /// \param nof_targets receives the estimated size of the write set
  ///
  void
  to_spec_frees_function(const irep_idt &function_id, std::size_t &nof_targets);

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  namespacet ns;

  /// Extracts the type of an assigns clause target expression
  /// The expression must be of the form:
  /// `expr = cast(address_of(target), empty*)`
  const typet &get_target_type(const exprt &expr);
};

#endif
