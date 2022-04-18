/*******************************************************************\

Module: Instrument assigns clauses in code contracts.

Author: Remi Delmas

Date: January 2022

\*******************************************************************/

/// \file
/// Specify write set in function contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_INSTRUMENT_SPEC_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_INSTRUMENT_SPEC_ASSIGNS_H

#include <optional>
#include <unordered_map>
#include <unordered_set>

#include <ansi-c/c_expr.h>

#include <goto-programs/goto_program.h>
#include <util/message.h>

#include "utils.h"

// forward declarations
class conditional_target_group_exprt;
class namespacet;
class symbol_tablet;
class symbolt;

/// Class that represents a single conditional target.
class conditional_target_exprt : public exprt
{
public:
  conditional_target_exprt(const exprt &_condition, const exprt &_target)
    : exprt(irep_idt{}, typet{}, {_condition, _target})
  {
    INVARIANT(
      !has_subexpr(_condition, ID_side_effect),
      "condition must have no side_effect sub-expression");
    add_source_location() = _target.source_location();
  }

  /// Condition expression
  const exprt &condition() const
  {
    return operands()[0];
  }

  /// Target expression
  const exprt &target() const
  {
    return operands()[1];
  }
};

/// method to use to havoc a target
enum class car_havoc_methodt
{
  HAVOC_OBJECT,
  HAVOC_SLICE,
  NONDET_ASSIGN
};

/// Class that represents a normalized conditional address range, with:
/// - condition expression
/// - target expression
/// - normalised start address expression
/// - normalised size expression
/// - snapshot variable symbols
class car_exprt : public exprt
{
public:
  car_exprt(
    const exprt &_condition,
    const exprt &_target,
    const exprt &_target_start_address,
    const exprt &_target_size,
    const symbol_exprt &_validity_var,
    const symbol_exprt &_lower_bound_var,
    const symbol_exprt &_upper_bound_var,
    const car_havoc_methodt _havoc_method)
    : exprt(
        irep_idt{},
        typet{},
        {_condition,
         _target,
         _target_start_address,
         _target_size,
         _validity_var,
         _lower_bound_var,
         _upper_bound_var}),
      havoc_method(_havoc_method)
  {
    add_source_location() = _target.source_location();
  }

  /// Method to use to havod the target
  const car_havoc_methodt havoc_method;

  /// Condition expression. When this condition holds the target is allowed
  const exprt &condition() const
  {
    return operands()[0];
  }

  /// The target expression
  const exprt &target() const
  {
    return operands()[1];
  }

  /// Start address of the target
  const exprt &target_start_address() const
  {
    return operands()[2];
  }

  /// Size of the target in bytes
  const exprt &target_size() const
  {
    return operands()[3];
  }

  /// Identifier of the validity snapshot variable
  const symbol_exprt &valid_var() const
  {
    return to_symbol_expr(operands()[4]);
  }

  /// Identifier of the lower address bound snapshot variable
  const symbol_exprt &lower_bound_var() const
  {
    return to_symbol_expr(operands()[5]);
  }

  /// Identifier of the upper address bound snapshot variable
  const symbol_exprt &upper_bound_var() const
  {
    return to_symbol_expr(operands()[6]);
  }
};

/// True iff the pragma to mark assignments to static local variables that need
/// to be propagated upwards in the search is set
bool has_propagate_static_local_pragma(source_locationt &source_location);

/// Sets a pragma to mark assignments to static local variables that need to be
/// propagated upwards in the search
void add_propagate_static_local_pragma(source_locationt &source_location);

/// \brief Adds a pragma on a source location disable all pointer checks.
///
/// The disabled checks are: "pointer-check", "pointer-primitive-check",
/// "pointer-overflow-check", "signed-overflow-check",
//  "unsigned-overflow-check", "conversion-check".
void add_pragma_disable_pointer_checks(source_locationt &source_location);

/// \brief Adds a pragma on a source_locationt to disable inclusion checking.
void add_pragma_disable_assigns_check(source_locationt &source_location);

/// \brief Adds a pragma on a GOTO instruction to disable inclusion checking.
///
/// \param instr: A mutable reference to the GOTO instruction.
/// \return The same reference after mutation (i.e., adding the pragma).
goto_programt::instructiont &
add_pragma_disable_assigns_check(goto_programt::instructiont &instr);

/// \brief Adds pragmas on all instructions in a GOTO program
///        to disable inclusion checking on them.
///
/// \param prog: A mutable reference to the GOTO program.
/// \return The same reference after mutation (i.e., adding the pragmas).
goto_programt &add_pragma_disable_assigns_check(goto_programt &prog);

/// Skip or do not skip assignments to function parameters
enum class skip_function_paramst
{
  YES,
  NO
};

/// \brief A class that generates instrumentation for assigns clause checking.
///
/// The `track_*` methods add targets to the sets of tracked targets and append
/// instructions to the given destination program.
///
/// The `check_inclusion_*` methods generate assertions checking for inclusion
/// of a designated target in one of the tracked targets,
/// and append instructions to the given destination.
class instrument_spec_assignst
{
public:
  /// \brief Class constructor.
  ///
  ///  \param _function_id name of the instrumented function
  ///  \param _functions other functions of the model
  ///  \param _st symbol table of the goto_model
  ///  \param _message_handler used to output warning/error messages
  instrument_spec_assignst(
    const irep_idt &_function_id,
    const goto_functionst &_functions,
    symbol_tablet &_st,
    message_handlert &_message_handler)
    : function_id(_function_id),
      functions(_functions),
      st(_st),
      ns(_st),
      log(_message_handler)
  {
  }

  /// Track an assigns clause target and generate snaphsot instructions
  /// and well-definedness assertions in dest.
  void track_spec_target(const exprt &expr, goto_programt &dest);

  /// Track a stack-allocated object and generate snaphsot instructions in dest.
  void
  track_stack_allocated(const symbol_exprt &symbol_expr, goto_programt &dest);

  /// Returns true if the expression is tracked.
  bool stack_allocated_is_tracked(const symbol_exprt &symbol_expr) const;

  /// Generate instructions to invalidate a
  /// stack-allocated object that goes DEAD in dest.
  void invalidate_stack_allocated(
    const symbol_exprt &symbol_expr,
    goto_programt &dest);

  /// Track a whole heap-alloc object and generate snaphsot instructions
  /// in dest.
  void track_heap_allocated(const exprt &expr, goto_programt &dest);

  /// Searches the goto instructions reachable from the start to the end of the
  /// instrumented function's instruction to identify local static variables,
  /// declared directly in the function or indirectly in the functions it calls,
  /// add them to the `stack-allocated` set of tracked locations, and generates
  /// corresponding snapshot instructions in dest.
  /// \param dest a snaphot program for the identified static locals.
  void track_static_locals(goto_programt &dest);

  /// Searches the goto instructions reachable between the given `it` and `end`
  /// target instructions to identify local static variables,
  /// declared directly in the function or indirectly in the functions it calls,
  /// add them to the `stack-allocated` set of tracked locations, and generates
  /// corresponding snapshot instructions in dest.
  /// \param it start instruction (inclusive)
  /// \param end end instruction (exclusive)
  /// \param dest a snaphot program for the identified static locals.
  void track_static_locals_between(
    goto_programt::const_targett it,
    const goto_programt::const_targett end,
    goto_programt &dest);

protected:
  /// \brief Represents an interval of source locations covered by the static
  /// local variable search.
  /// Interval bounds are represented with (line, col) positive integers.
  /// Lexicographic ordering is used for comparisons.
  /// Updates to the bounds and inclusion checks use pessimistic defaults
  /// when source locations are undefined or only partially defined.
  class location_intervalt
  {
  public:
    /// Initializes to the empty interval
    location_intervalt()
    {
      min_line = std::numeric_limits<std::size_t>::max();
      min_col = std::numeric_limits<std::size_t>::max();
      max_line = std::numeric_limits<std::size_t>::min();
      max_col = std::numeric_limits<std::size_t>::min();
    }

    /// Grows the interval cover the maximum range
    /// [(size_t::min, size_t::min), (size_t::min, size_t::max)]
    void anywhere()
    {
      min_line = std::numeric_limits<std::size_t>::min();
      min_col = std::numeric_limits<std::size_t>::min();
      max_line = std::numeric_limits<std::size_t>::max();
      max_col = std::numeric_limits<std::size_t>::max();
    }

    /// Grows the interval to include the given (line, col) location
    void update(const source_locationt &source_location)
    {
      PRECONDITION(source_location.is_not_nil());
      // use pessimistic lowest value to update min for undefined
      update_min(
        line_to_size_t(
          source_location, std::numeric_limits<std::size_t>::min()),
        col_to_size_t(
          source_location, std::numeric_limits<std::size_t>::min()));

      // use pessimistic highest value to update max for undefined
      update_max(
        line_to_size_t(
          source_location, std::numeric_limits<std::size_t>::max()),
        col_to_size_t(
          source_location, std::numeric_limits<std::size_t>::max()));
    }

    /// True iff the interval contains the given location
    bool contains(const source_locationt &source_location)
    {
      if(source_location.is_not_nil())
      {
        return
          // use pessimistic highest value to compare to min for undefined
          is_lte(
            min_line,
            min_col,
            line_to_size_t(
              source_location, std::numeric_limits<std::size_t>::max()),
            col_to_size_t(
              source_location, std::numeric_limits<std::size_t>::max())) &&
          // use pessimistic lowest value to compare to max for undefined
          is_lte(
            line_to_size_t(
              source_location, std::numeric_limits<std::size_t>::min()),
            col_to_size_t(
              source_location, std::numeric_limits<std::size_t>::min()),
            max_line,
            max_col);
      }
      else
      {
        return true;
      }
    }

  private:
    /// If line or col is missing use default
    std::size_t col_to_size_t(
      const source_locationt &source_location,
      std::size_t default_value)
    {
      if(
        source_location.get_line().empty() ||
        source_location.get_column().empty())
      {
        return default_value;
      }
      else
      {
        std::stringstream stream(id2string(source_location.get_column()));
        size_t res;
        stream >> res;
        return res;
      }
    }

    /// If line is missing use default
    std::size_t line_to_size_t(
      const source_locationt &source_location,
      std::size_t default_value)
    {
      if(source_location.get_line().empty())
      {
        return default_value;
      }
      else
      {
        std::stringstream stream(id2string(source_location.get_line()));
        size_t res;
        stream >> res;
        return res;
      }
    }

    /// True iff `(line0, col0) <= (line1, col1)` in lexicographic ordering
    static bool is_lte(size_t line0, size_t col0, size_t line1, size_t col1)
    {
      return (line0 < line1) || ((line0 == line1) && (col0 <= col1));
    }

    /// Updates the min_line and min_col in place using the given values
    /// iff they are smaller.
    void update_min(size_t line, size_t col)
    {
      if(is_lte(line, col, min_line, min_col))
      {
        min_line = line;
        min_col = col;
      }
    }

    /// Updates the max_line and max_col in place using the given values
    /// iff they are larger.
    void update_max(size_t line, size_t col)
    {
      if(is_lte(max_line, max_col, line, col))
      {
        max_line = line;
        max_col = col;
      }
    }

    std::size_t min_line;
    std::size_t min_col;
    std::size_t max_line;
    std::size_t max_col;
  };

  /// Map type from function identifiers to covered locations
  typedef std::unordered_map<irep_idt, location_intervalt> covered_locationst;
  typedef std::unordered_set<symbol_exprt, irep_hash> propagated_static_localst;

  /// Traverses the given list of instructions, updating the given
  /// coverage map, recursing into function calls only once.
  /// When the traversal terminates, the map will contain one
  /// entry per visited function, with the associated range of locations
  /// covered by the traversal.
  /// Function names and line numbers are collected from source
  /// locations attached to the instructions.
  void traverse_instructions(
    const irep_idt ambient_function_id,
    goto_programt::const_targett it,
    const goto_programt::const_targett end,
    covered_locationst &covered_locations,
    propagated_static_localst &propagated) const;

  /// Collects static symbols from the symbol table that have a source location
  /// included in one of the `covered_locations` and writes them into dest.
  void collect_static_symbols(
    covered_locationst &covered_locations,
    std::unordered_set<symbol_exprt, irep_hash> &dest);

public:
  /// Generates inclusion check instructions for an assignment, havoc or
  /// havoc_object instruction
  /// \param lhs the assignment lhs or argument to havoc/havoc_object
  /// \param cfg_info_opt allows target set pruning if available
  /// \param dest destination program to append instructions to
  ///
  /// \remark if provided, the internal instruction pointer of
  /// `cfg_info_opt::target()` must point to the instruction containing the lhs
  ///  in question.
  void check_inclusion_assignment(
    const exprt &lhs,
    optionalt<cfg_infot> &cfg_info_opt,
    goto_programt &dest) const;

  /// Generates inclusion check instructions for an argument passed to free
  /// \param expr the argument to the free operator
  /// \param cfg_info_opt allows target set pruning if available
  /// \param dest destination program to append instructions to
  ///
  /// \remark If provided, the internal instruction pointer of
  /// `cfg_info_opt::target()` must point to the instruction containing the lhs
  ///  in question.
  void check_inclusion_heap_allocated_and_invalidate_aliases(
    const exprt &expr,
    optionalt<cfg_infot> &cfg_info_opt,
    goto_programt &dest);

  /// Instruments a sequence of instructions with inclusion checks.
  ///   If `pred` is not provided,
  ///     then all instructions are instrumented.
  ///   If `pred` is provided,
  ///     then only the instructions that satisfy pred are instrumented.
  ///
  /// \param body goto program containing the instructions
  /// \param instruction_it target to the first instruction of the sequence
  /// \param instruction_end target to the last instruction of the sequence
  /// \param skip_function_params the argument to the free operator
  /// \param cfg_info_opt allows target set pruning if available
  /// \param pred a predicate on targets to check if they should be instrumented
  void instrument_instructions(
    goto_programt &body,
    goto_programt::targett instruction_it,
    const goto_programt::targett &instruction_end,
    skip_function_paramst skip_function_params,
    optionalt<cfg_infot> &cfg_info_opt,
    const std::function<bool(const goto_programt::targett &)> &pred = {});

  /// Inserts the detected static local symbols into a target container.
  /// \tparam C The type of the target container
  /// \param inserter An insert_iterator on the target container
  template <typename C>
  void get_static_locals(std::insert_iterator<C> inserter) const
  {
    std::transform(
      from_static_local.cbegin(),
      from_static_local.cend(),
      inserter,
      // can use `const auto &` below once we switch to C++14
      [](const symbol_exprt_to_car_mapt::value_type &s) { return s.first; });
  }

protected:
  /// Name of the instrumented function
  const irep_idt &function_id;

  /// Other functions of the model
  const goto_functionst &functions;

  /// Program symbol table
  symbol_tablet &st;

  /// Program namespace
  const namespacet ns;

  /// Logger
  messaget log;

  /// Track and generate snaphsot instructions and target validity
  /// checking assertions for a conditional target group from an assigns clause
  void track_spec_target_group(
    const conditional_target_group_exprt &group,
    goto_programt &dest);

  /// Track and generate snaphsot instructions and target validity
  /// checking assertions for a conditional target group from an assigns clause
  void track_plain_spec_target(const exprt &expr, goto_programt &dest);

  /// Creates a fresh symbolt with given suffix,
  /// scoped to \ref function_id.
  const symbolt create_fresh_symbol(
    const std::string &suffix,
    const typet &type,
    const source_locationt &location) const;

  /// Returns snapshot instructions for a car_exprt
  void create_snapshot(const car_exprt &car, goto_programt &dest) const;

  /// Returns the target validity expression for a car_exprt
  exprt
  target_validity_expr(const car_exprt &car, bool allow_null_target) const;

  /// Generates the target validity assertion for the given `car` and adds
  /// it to `dest`.
  /// The assertion checks that if the car's condition holds then
  /// the target is `r_ok` (or `NULL` if `allow_null_targets` is true).
  void target_validity_assertion(
    const car_exprt &car,
    bool allow_null_target,
    goto_programt &dest) const;

  /// Returns inclusion check expression for a single candidate location
  exprt inclusion_check_single(
    const car_exprt &lhs,
    const car_exprt &candidate_car) const;

  /// Returns an inclusion check expression of lhs over all tracked cars.
  /// \param lhs the lhs expression to check for inclusion
  /// \param allow_null_lhs if true, allow the lhs to be NULL
  /// \param include_stack_allocated if true, include stack allocated targets
  /// in the inclusion check.
  /// \param cfg_info_opt allows target set pruning if available
  /// \remark If available, `cfg_info_opt` must point to the `lhs` in question.
  exprt inclusion_check_full(
    const car_exprt &lhs,
    bool allow_null_lhs,
    bool include_stack_allocated,
    optionalt<cfg_infot> &cfg_info_opt) const;

  /// Returns an inclusion check assertion of lhs over all tracked cars.
  /// \param lhs the lhs expression to check for inclusion
  /// \param allow_null_lhs if true, allow the lhs to be NULL
  /// \param include_stack_allocated if true, include stack allocated targets
  /// in the inclusion check.
  /// \param cfg_info_opt allows target set pruning if available
  /// \param dest destination program to append instructions to
  /// \remark If available, `cfg_info_opt` must point to the `lhs` in question.
  void inclusion_check_assertion(
    const car_exprt &lhs,
    bool allow_null_lhs,
    bool include_stack_allocated,
    optionalt<cfg_infot> &cfg_info_opt,
    goto_programt &dest) const;

  /// \brief Adds an assignment in dest to invalidate the tracked car if
  /// was valid before and was pointing to the same object as the freed car.
  void invalidate_car(
    const car_exprt &tracked_car,
    const car_exprt &freed_car,
    goto_programt &result) const;

  /// Generates instructions to invalidate all targets aliased with a
  /// car that was passed to `free`, assuming the inclusion check passes,
  /// ie. that the freed_car is fully included in one of the tracked targets.
  void invalidate_heap_and_spec_aliases(
    const car_exprt &freed_car,
    goto_programt &dest) const;

  /// Returns true iff a `DECL x` must be added to the local write set.
  ///
  /// A variable is called 'dirty' if its address gets taken at some point in
  /// the program.
  ///
  /// Assuming the goto program is obtained from a structured C program that
  /// passed C compiler checks, non-dirty variables can only be assigned to
  /// directly by name, cannot escape their lexical scope, and are always safe
  /// to assign. Hence, we only track dirty variables in the write set.
  bool must_track_decl(
    const goto_programt::const_targett &target,
    const optionalt<cfg_infot> &cfg_info_opt) const;

  /// Returns true iff a `DEAD x` must be processed to update the local write
  /// set. The conditions are the same than for tracking a `DECL x` instruction.
  bool must_track_dead(
    const goto_programt::const_targett &target,
    const optionalt<cfg_infot> &cfg_info_opt) const;

  /// Returns true iff an `ASSIGN lhs := rhs` instruction must be instrumented.
  bool must_check_assign(
    const goto_programt::const_targett &target,
    skip_function_paramst skip_function_params,
    const optionalt<cfg_infot> cfg_info_opt);

  /// Inserts an assertion in `body` immediately before the assignment
  /// at `instruction_it`, to ensure that the LHS of the assignment
  /// is included in the set of currently tracked CARs.
  void instrument_assign_statement(
    goto_programt::targett &instruction_it,
    goto_programt &body,
    optionalt<cfg_infot> &cfg_info_opt) const;

  /// Inserts an assertion in `body` immediately before the function call at
  /// `instruction_it`, to ensure that all memory locations written to by the
  /// called function are included in the set of currently tracked CARs.
  void instrument_call_statement(
    goto_programt::targett &instruction_it,
    goto_programt &body,
    optionalt<cfg_infot> &cfg_info_opt);

  using cond_target_exprt_to_car_mapt = std::
    unordered_map<const conditional_target_exprt, const car_exprt, irep_hash>;

  /// Map from conditional target expressions of assigns clauses
  /// to corresponding conditional address ranges.
  cond_target_exprt_to_car_mapt from_spec_assigns;

  const car_exprt &
  create_car_from_spec_assigns(const exprt &condition, const exprt &target);

  using symbol_exprt_to_car_mapt =
    std::unordered_map<const symbol_exprt, const car_exprt, irep_hash>;

  /// Map from DECL symbols to corresponding conditional address ranges.
  symbol_exprt_to_car_mapt from_stack_alloc;

  const car_exprt &create_car_from_stack_alloc(const symbol_exprt &target);

  using exprt_to_car_mapt =
    std::unordered_map<const exprt, const car_exprt, irep_hash>;

  /// Map from malloc'd symbols to corresponding conditional address ranges.
  exprt_to_car_mapt from_heap_alloc;

  const car_exprt &create_car_from_heap_alloc(const exprt &target);

  /// Map to from detected or propagated static local symbols to corresponding
  /// conditional address ranges.
  symbol_exprt_to_car_mapt from_static_local;

  const car_exprt &create_car_from_static_local(const symbol_exprt &target);

  /// Creates a conditional address range expression from a cleaned-up condition
  /// and target expression.
  car_exprt create_car_expr(const exprt &condition, const exprt &target) const;
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_INSTRUMENT_SPEC_ASSIGNS_H
