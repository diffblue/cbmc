/*******************************************************************\

Module: Checks for Errors in C/C++ Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Checks for Errors in C/C++ Programs

#include "goto_check_c.h"

#include <util/arith_tools.h>
#include <util/array_name.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <analyses/local_bitvector_analysis.h>
#include <langapi/language.h>
#include <langapi/mode.h>

#include <ansi-c/c_expr.h>

#include <algorithm>

class goto_check_ct
{
public:
  goto_check_ct(
    const namespacet &_ns,
    const optionst &_options,
    message_handlert &_message_handler)
    : ns(_ns), local_bitvector_analysis(nullptr), log(_message_handler)
  {
    enable_bounds_check = _options.get_bool_option("bounds-check");
    enable_pointer_check = _options.get_bool_option("pointer-check");
    enable_memory_leak_check = _options.get_bool_option("memory-leak-check");
    enable_memory_cleanup_check =
      _options.get_bool_option("memory-cleanup-check");
    enable_div_by_zero_check = _options.get_bool_option("div-by-zero-check");
    enable_float_div_by_zero_check =
      _options.get_bool_option("float-div-by-zero-check");
    enable_enum_range_check = _options.get_bool_option("enum-range-check");
    enable_signed_overflow_check =
      _options.get_bool_option("signed-overflow-check");
    enable_unsigned_overflow_check =
      _options.get_bool_option("unsigned-overflow-check");
    enable_pointer_overflow_check =
      _options.get_bool_option("pointer-overflow-check");
    enable_conversion_check = _options.get_bool_option("conversion-check");
    enable_undefined_shift_check =
      _options.get_bool_option("undefined-shift-check");
    enable_float_overflow_check =
      _options.get_bool_option("float-overflow-check");
    enable_simplify = _options.get_bool_option("simplify");
    enable_nan_check = _options.get_bool_option("nan-check");
    retain_trivial = _options.get_bool_option("retain-trivial-checks");
    enable_assert_to_assume = _options.get_bool_option("assert-to-assume");
    error_labels = _options.get_list_option("error-label");
    enable_pointer_primitive_check =
      _options.get_bool_option("pointer-primitive-check");
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  void goto_check(
    const irep_idt &function_identifier,
    goto_functiont &goto_function);

  /// Fill the list of allocations \ref allocationst with <address, size> for
  ///   every allocation instruction. Also check that each allocation is
  ///   well-formed.
  /// \param goto_functions: goto functions from which the allocations are to be
  ///   collected
  void collect_allocations(const goto_functionst &goto_functions);

protected:
  const namespacet &ns;
  std::unique_ptr<local_bitvector_analysist> local_bitvector_analysis;
  goto_programt::const_targett current_target;
  messaget log;

  using guardt = std::function<exprt(exprt)>;
  const guardt identity = [](exprt expr) { return expr; };

  void check_shadow_memory_api_calls(const goto_programt::instructiont &);

  /// Check an address-of expression:
  ///  if it is a dereference then check the pointer
  ///  if it is an index then address-check the array and then check the index
  /// \param expr: the expression to be checked
  /// \param guard: the condition for the check
  void check_rec_address(const exprt &expr, const guardt &guard);

  /// Check a logical operation: check each operand in separation while
  /// extending the guarding condition as follows.
  ///  a /\ b /\ c ==> check(a, TRUE), check(b, a), check (c, a /\ b)
  ///  a \/ b \/ c ==> check(a, TRUE), check(b, ~a), check (c, ~a /\ ~b)
  /// \param expr: the expression to be checked
  /// \param guard: the condition for the check (extended with the previous
  ///   operands (or their negations) for recursively calls)
  void check_rec_logical_op(const exprt &expr, const guardt &guard);

  /// Check an if expression: check the if-condition alone, and then check the
  ///   true/false-cases with the guard extended with if-condition and it's
  ///   negation, respectively.
  /// \param if_expr: the expression to be checked
  /// \param guard: the condition for the check (extended with the (negation of
  ///   the) if-condition for recursively calls)
  void check_rec_if(const if_exprt &if_expr, const guardt &guard);

  /// Check that a member expression is valid:
  /// - check the structure this expression is a member of (via pointer of its
  ///   dereference)
  /// - run pointer-validity check on `*(s+member_offset)' instead of
  ///   `s->member' to avoid checking safety of `s'
  /// - check all operands of the expression
  /// \param member: the expression to be checked
  /// \param guard: the condition for the check
  /// \return true if no more checks are required for \p member or its
  ///   sub-expressions
  bool check_rec_member(const member_exprt &member, const guardt &guard);

  /// Check that a division is valid: check for division by zero, overflow and
  ///   NaN (for floating point numbers).
  /// \param div_expr: the expression to be checked
  /// \param guard: the condition for the check
  void check_rec_div(const div_exprt &div_expr, const guardt &guard);

  /// Check that an arithmetic operation is valid: overflow check, NaN-check
  ///   (for floating point numbers), and pointer overflow check.
  /// \param expr: the expression to be checked
  /// \param guard: the condition for the check
  void check_rec_arithmetic_op(const exprt &expr, const guardt &guard);

  /// Recursively descend into \p expr and run the appropriate check for each
  ///   sub-expression, while collecting the condition for the check in \p
  ///   guard.
  /// \param expr: the expression to be checked
  /// \param guard: the condition for when the check should be made
  void check_rec(const exprt &expr, const guardt &guard);

  /// Initiate the recursively analysis of \p expr with its `guard' set to TRUE.
  /// \param expr: the expression to be checked
  void check(const exprt &expr);

  struct conditiont
  {
    conditiont(const exprt &_assertion, const std::string &_description)
      : assertion(_assertion), description(_description)
    {
    }

    exprt assertion;
    std::string description;
  };

  using conditionst = std::list<conditiont>;

  void bounds_check(const exprt &, const guardt &);
  void bounds_check_index(const index_exprt &, const guardt &);
  void bounds_check_bit_count(const unary_exprt &, const guardt &);
  void div_by_zero_check(const div_exprt &, const guardt &);
  void float_div_by_zero_check(const div_exprt &, const guardt &);
  void mod_by_zero_check(const mod_exprt &, const guardt &);
  void mod_overflow_check(const mod_exprt &, const guardt &);
  void enum_range_check(const exprt &, const guardt &);
  void undefined_shift_check(const shift_exprt &, const guardt &);
  void pointer_rel_check(const binary_exprt &, const guardt &);
  void pointer_overflow_check(const exprt &, const guardt &);
  void memory_leak_check(const irep_idt &function_id);

  /// Generates VCCs for the validity of the given dereferencing operation.
  /// \param expr the expression to be checked
  /// \param src_expr The expression as found in the program,
  ///  prior to any rewriting
  /// \param guard the condition under which the operation happens
  void pointer_validity_check(
    const dereference_exprt &expr,
    const exprt &src_expr,
    const guardt &guard);

  /// Generates VCCs to check that pointers passed to pointer primitives are
  /// either null or valid
  ///
  /// \param expr: the pointer primitive expression
  /// \param guard: the condition under which the operation happens
  void pointer_primitive_check(const exprt &expr, const guardt &guard);

  /// Returns true if the given expression is a pointer primitive
  /// that requires validation of the operand to guard against misuse
  ///
  /// \param expr expression
  /// \return true if the given expression is a pointer primitive that requires
  ///   checking
  bool requires_pointer_primitive_check(const exprt &expr);

  std::optional<goto_check_ct::conditiont>
  get_pointer_is_null_condition(const exprt &address, const exprt &size);
  conditionst get_pointer_points_to_valid_memory_conditions(
    const exprt &address,
    const exprt &size);
  exprt is_in_bounds_of_some_explicit_allocation(
    const exprt &pointer,
    const exprt &size);

  conditionst get_pointer_dereferenceable_conditions(
    const exprt &address,
    const exprt &size);
  void integer_overflow_check(const exprt &, const guardt &);
  void conversion_check(const exprt &, const guardt &);
  void float_overflow_check(const exprt &, const guardt &);
  void nan_check(const exprt &, const guardt &);

  std::string array_name(const exprt &);

  /// Include the \p asserted_expr in the code conditioned by the \p guard.
  /// \param asserted_expr: expression to be asserted
  /// \param comment: human readable comment
  /// \param property_class: classification of the property
  /// \param source_location: the source location of the original expression
  /// \param src_expr: the original expression to be included in the comment
  /// \param guard: the condition under which the asserted expression should be
  ///   taken into account
  void add_guarded_property(
    const exprt &asserted_expr,
    const std::string &comment,
    const std::string &property_class,
    const source_locationt &source_location,
    const exprt &src_expr,
    const guardt &guard);

  goto_programt new_code;
  typedef std::set<std::pair<exprt, exprt>> assertionst;
  assertionst assertions;

  /// Remove all assertions containing the symbol in \p lhs as well as all
  ///   assertions containing dereference.
  /// \param lhs: the left-hand-side expression whose symbol should be
  ///   invalidated
  void invalidate(const exprt &lhs);

  bool enable_bounds_check;
  bool enable_pointer_check;
  bool enable_memory_leak_check;
  bool enable_memory_cleanup_check;
  bool enable_div_by_zero_check;
  bool enable_float_div_by_zero_check;
  bool enable_enum_range_check;
  bool enable_signed_overflow_check;
  bool enable_unsigned_overflow_check;
  bool enable_pointer_overflow_check;
  bool enable_conversion_check;
  bool enable_undefined_shift_check;
  bool enable_float_overflow_check;
  bool enable_simplify;
  bool enable_nan_check;
  bool retain_trivial;
  bool enable_assert_to_assume;
  bool enable_pointer_primitive_check;

  /// Maps a named-check name to the corresponding boolean flag.
  std::map<irep_idt, bool *> name_to_flag{
    {"bounds-check", &enable_bounds_check},
    {"pointer-check", &enable_pointer_check},
    {"memory-leak-check", &enable_memory_leak_check},
    {"memory-cleanup-check", &enable_memory_cleanup_check},
    {"div-by-zero-check", &enable_div_by_zero_check},
    {"float-div-by-zero-check", &enable_float_div_by_zero_check},
    {"enum-range-check", &enable_enum_range_check},
    {"signed-overflow-check", &enable_signed_overflow_check},
    {"unsigned-overflow-check", &enable_unsigned_overflow_check},
    {"pointer-overflow-check", &enable_pointer_overflow_check},
    {"conversion-check", &enable_conversion_check},
    {"undefined-shift-check", &enable_undefined_shift_check},
    {"float-overflow-check", &enable_float_overflow_check},
    {"nan-check", &enable_nan_check},
    {"pointer-primitive-check", &enable_pointer_primitive_check}};

  typedef optionst::value_listt error_labelst;
  error_labelst error_labels;

  // the first element of the pair is the base address,
  // and the second is the size of the region
  typedef std::pair<exprt, exprt> allocationt;
  typedef std::list<allocationt> allocationst;
  allocationst allocations;

  irep_idt mode;

  /// \brief Adds "checked" pragmas for all currently active named checks
  /// on the given source location.
  void add_active_named_check_pragmas(source_locationt &source_location) const;

  /// \brief Adds "checked" pragmas for all named checks on the given source
  /// location (prevents any the instanciation of any ulterior check).
  void
  add_all_checked_named_check_pragmas(source_locationt &source_location) const;

  /// activation statuses for named checks
  typedef enum
  {
    ENABLE,
    DISABLE,
    CHECKED
  } check_statust;

  /// optional (named-check, status) pair
  using named_check_statust = std::optional<std::pair<irep_idt, check_statust>>;

  /// Matches a named-check string of the form
  ///
  /// ```
  /// ("enable"|"disable"|"checked") ":" <named-check>
  /// ```
  ///
  /// \returns a pair (name, status) if the match succeeds
  /// and the name is known, nothing otherwise.
  named_check_statust match_named_check(const irep_idt &named_check) const;
};

/// Allows to:
/// - override a Boolean flag with a new value via `set_flag`
/// - set a Boolean flag to false via `disable_flag`, such that
///   previous `set_flag` are overridden and future `set_flag` are ignored.
///
/// A flag's initial value (before any `set_flag` or `disable_flag`) is restored
/// when the entire object goes out of scope.
class flag_overridet
{
public:
  explicit flag_overridet(const source_locationt &source_location)
    : source_location(source_location)
  {
  }

  /// \brief Store the current value of \p flag and
  /// then set its value to \p new_value.
  ///
  /// - calling `set_flag` after `disable_flag` is a no-op
  /// - calling `set_flag` twice triggers an INVARIANT
  void set_flag(bool &flag, bool new_value, const irep_idt &flag_name)
  {
    // make this a no-op if the flag is disabled
    if(disabled_flags.find(&flag) != disabled_flags.end())
      return;

    // detect double sets
    INVARIANT(
      flags_to_reset.find(&flag) == flags_to_reset.end(),
      "Flag " + id2string(flag_name) + " set twice at \n" +
        source_location.as_string());
    if(flag != new_value)
    {
      flags_to_reset[&flag] = flag;
      flag = new_value;
    }
  }

  /// Sets the given flag to false, overriding any previous value.
  ///
  /// - calling `disable_flag` after `set_flag` overrides the set value
  /// - calling `disable_flag` twice triggers an INVARIANT
  void disable_flag(bool &flag, const irep_idt &flag_name)
  {
    INVARIANT(
      disabled_flags.find(&flag) == disabled_flags.end(),
      "Flag " + id2string(flag_name) + " disabled twice at \n" +
        source_location.as_string());

    disabled_flags.insert(&flag);

    // If the flag has not already been set,
    // we store its current value in the reset map.
    // Otherwise, the reset map already holds
    // the initial value we want to reset it to, keep it as is.
    if(flags_to_reset.find(&flag) == flags_to_reset.end())
      flags_to_reset[&flag] = flag;

    // set the flag to false in all cases.
    flag = false;
  }

  /// \brief Restore the values of all flags that have been
  /// modified via `set_flag`.
  ~flag_overridet()
  {
    for(const auto &flag_pair : flags_to_reset)
      *flag_pair.first = flag_pair.second;
  }

private:
  const source_locationt &source_location;
  std::map<bool *, bool> flags_to_reset;
  std::set<bool *> disabled_flags;
};

static exprt implication(exprt lhs, exprt rhs)
{
  // rewrite a => (b => c) to (a && b) => c
  if(rhs.id() == ID_implies)
  {
    const auto &rhs_implication = to_implies_expr(rhs);
    return implies_exprt(
      and_exprt(std::move(lhs), rhs_implication.lhs()), rhs_implication.rhs());
  }
  else
  {
    return implies_exprt(std::move(lhs), std::move(rhs));
  }
}

void goto_check_ct::collect_allocations(const goto_functionst &goto_functions)
{
  for(const auto &gf_entry : goto_functions.function_map)
  {
    for(const auto &instruction : gf_entry.second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;

      const auto &function = instruction.call_function();
      if(
        function.id() != ID_symbol ||
        to_symbol_expr(function).get_identifier() != CPROVER_PREFIX
          "allocated_memory")
        continue;

      const code_function_callt::argumentst &args =
        instruction.call_arguments();
      if(
        args.size() != 2 || args[0].type().id() != ID_unsignedbv ||
        args[1].type().id() != ID_unsignedbv)
        throw "expected two unsigned arguments to " CPROVER_PREFIX
              "allocated_memory";

      DATA_INVARIANT(
        args[0].type() == args[1].type(),
        "arguments of allocated_memory must have same type");
      allocations.push_back({args[0], args[1]});
    }
  }
}

void goto_check_ct::invalidate(const exprt &lhs)
{
  if(lhs.id() == ID_index)
    invalidate(to_index_expr(lhs).array());
  else if(lhs.id() == ID_member)
    invalidate(to_member_expr(lhs).struct_op());
  else if(lhs.id() == ID_symbol)
  {
    // clear all assertions about 'symbol'
    const irep_idt &lhs_id = to_symbol_expr(lhs).get_identifier();

    for(auto it = assertions.begin(); it != assertions.end();)
    {
      if(
        has_symbol_expr(it->second, lhs_id, false) ||
        has_subexpr(it->second, ID_dereference))
      {
        it = assertions.erase(it);
      }
      else
        ++it;
    }
  }
  else
  {
    // give up, clear all
    assertions.clear();
  }
}

void goto_check_ct::div_by_zero_check(
  const div_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero = from_integer(0, expr.op1().type());
  const notequal_exprt inequality(expr.op1(), std::move(zero));

  add_guarded_property(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_check_ct::float_div_by_zero_check(
  const div_exprt &expr,
  const guardt &guard)
{
  if(!enable_float_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero = from_integer(0, expr.op1().type());
  const notequal_exprt inequality(expr.op1(), std::move(zero));

  add_guarded_property(
    inequality,
    "floating-point division by zero",
    "float-division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_check_ct::enum_range_check(const exprt &expr, const guardt &guard)
{
  if(!enable_enum_range_check)
    return;

  // we might be looking at a lowered enum_is_in_range_exprt, skip over these
  const auto &pragmas = expr.source_location().get_pragmas();
  for(const auto &d : pragmas)
  {
    if(d.first == "disable:enum-range-check")
      return;
  }

  const exprt check = enum_is_in_range_exprt{expr}.lower(ns);

  add_guarded_property(
    check,
    "enum range check",
    "enum-range-check",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_check_ct::undefined_shift_check(
  const shift_exprt &expr,
  const guardt &guard)
{
  if(!enable_undefined_shift_check)
    return;

  // Undefined for all types and shifts if distance exceeds width,
  // and also undefined for negative distances.

  const typet &distance_type = expr.distance().type();

  if(distance_type.id() == ID_signedbv)
  {
    binary_relation_exprt inequality(
      expr.distance(), ID_ge, from_integer(0, distance_type));

    add_guarded_property(
      inequality,
      "shift distance is negative",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);
  }

  const typet &op_type = expr.op().type();

  if(op_type.id() == ID_unsignedbv || op_type.id() == ID_signedbv)
  {
    exprt width_expr =
      from_integer(to_bitvector_type(op_type).get_width(), distance_type);

    add_guarded_property(
      binary_relation_exprt(expr.distance(), ID_lt, std::move(width_expr)),
      "shift distance too large",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);

    if(op_type.id() == ID_signedbv && expr.id() == ID_shl)
    {
      binary_relation_exprt inequality(
        expr.op(), ID_ge, from_integer(0, op_type));

      add_guarded_property(
        inequality,
        "shift operand is negative",
        "undefined-shift",
        expr.find_source_location(),
        expr,
        guard);
    }
  }
  else
  {
    add_guarded_property(
      false_exprt(),
      "shift of non-integer type",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_ct::mod_by_zero_check(
  const mod_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero = from_integer(0, expr.divisor().type());
  const notequal_exprt inequality(expr.divisor(), std::move(zero));

  add_guarded_property(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

/// check a mod expression for the case INT_MIN % -1
void goto_check_ct::mod_overflow_check(
  const mod_exprt &expr,
  const guardt &guard)
{
  if(!enable_signed_overflow_check)
    return;

  const auto &type = expr.type();

  if(type.id() == ID_signedbv)
  {
    // INT_MIN % -1 is, in principle, defined to be zero in
    // ANSI C, C99, C++98, and C++11. Most compilers, however,
    // fail to produce 0, and in some cases generate an exception.
    // C11 explicitly makes this case undefined.

    notequal_exprt int_min_neq(
      expr.op0(), to_signedbv_type(type).smallest_expr());

    notequal_exprt minus_one_neq(
      expr.op1(), from_integer(-1, expr.op1().type()));

    add_guarded_property(
      or_exprt(int_min_neq, minus_one_neq),
      "result of signed mod is not representable",
      "overflow",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_ct::conversion_check(const exprt &expr, const guardt &guard)
{
  if(!enable_conversion_check)
    return;

  // First, check type.
  const typet &type = expr.type();

  if(type.id() != ID_signedbv && type.id() != ID_unsignedbv)
    return;

  if(expr.id() == ID_typecast)
  {
    const auto &op = to_typecast_expr(expr).op();

    // conversion to signed int may overflow
    const typet &old_type = op.type();

    if(type.id() == ID_signedbv)
    {
      std::size_t new_width = to_signedbv_type(type).get_width();

      if(old_type.id() == ID_signedbv) // signed -> signed
      {
        std::size_t old_width = to_signedbv_type(old_type).get_width();
        if(new_width >= old_width)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          op, ID_le, from_integer(power(2, new_width - 1) - 1, old_type));

        const binary_relation_exprt no_overflow_lower(
          op, ID_ge, from_integer(-power(2, new_width - 1), old_type));

        add_guarded_property(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on signed type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id() == ID_unsignedbv) // unsigned -> signed
      {
        std::size_t old_width = to_unsignedbv_type(old_type).get_width();
        if(new_width >= old_width + 1)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          op, ID_le, from_integer(power(2, new_width - 1) - 1, old_type));

        add_guarded_property(
          no_overflow_upper,
          "arithmetic overflow on unsigned to signed type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id() == ID_floatbv) // float -> signed
      {
        // Note that the fractional part is truncated!
        ieee_floatt upper(to_floatbv_type(old_type));
        upper.from_integer(power(2, new_width - 1));
        const binary_relation_exprt no_overflow_upper(
          op, ID_lt, upper.to_expr());

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-power(2, new_width - 1) - 1);
        const binary_relation_exprt no_overflow_lower(
          op, ID_gt, lower.to_expr());

        add_guarded_property(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on float to signed integer type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
    }
    else if(type.id() == ID_unsignedbv)
    {
      std::size_t new_width = to_unsignedbv_type(type).get_width();

      if(old_type.id() == ID_signedbv) // signed -> unsigned
      {
        std::size_t old_width = to_signedbv_type(old_type).get_width();

        if(new_width >= old_width - 1)
        {
          // only need lower bound check
          const binary_relation_exprt no_overflow_lower(
            op, ID_ge, from_integer(0, old_type));

          add_guarded_property(
            no_overflow_lower,
            "arithmetic overflow on signed to unsigned type conversion",
            "overflow",
            expr.find_source_location(),
            expr,
            guard);
        }
        else
        {
          // need both
          const binary_relation_exprt no_overflow_upper(
            op, ID_le, from_integer(power(2, new_width) - 1, old_type));

          const binary_relation_exprt no_overflow_lower(
            op, ID_ge, from_integer(0, old_type));

          add_guarded_property(
            and_exprt(no_overflow_lower, no_overflow_upper),
            "arithmetic overflow on signed to unsigned type conversion",
            "overflow",
            expr.find_source_location(),
            expr,
            guard);
        }
      }
      else if(old_type.id() == ID_unsignedbv) // unsigned -> unsigned
      {
        std::size_t old_width = to_unsignedbv_type(old_type).get_width();
        if(new_width >= old_width)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          op, ID_le, from_integer(power(2, new_width) - 1, old_type));

        add_guarded_property(
          no_overflow_upper,
          "arithmetic overflow on unsigned to unsigned type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id() == ID_floatbv) // float -> unsigned
      {
        // Note that the fractional part is truncated!
        ieee_floatt upper(to_floatbv_type(old_type));
        upper.from_integer(power(2, new_width));
        const binary_relation_exprt no_overflow_upper(
          op, ID_lt, upper.to_expr());

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-1);
        const binary_relation_exprt no_overflow_lower(
          op, ID_gt, lower.to_expr());

        add_guarded_property(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on float to unsigned integer type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
    }
  }
}

void goto_check_ct::integer_overflow_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_signed_overflow_check && !enable_unsigned_overflow_check)
    return;

  // First, check type.
  const typet &type = expr.type();

  if(type.id() == ID_signedbv && !enable_signed_overflow_check)
    return;

  if(type.id() == ID_unsignedbv && !enable_unsigned_overflow_check)
    return;

  // add overflow subgoal

  if(expr.id() == ID_div)
  {
    // undefined for signed division INT_MIN/-1
    if(type.id() == ID_signedbv)
    {
      const auto &div_expr = to_div_expr(expr);

      equal_exprt int_min_eq(
        div_expr.dividend(), to_signedbv_type(type).smallest_expr());

      equal_exprt minus_one_eq(div_expr.divisor(), from_integer(-1, type));

      add_guarded_property(
        not_exprt(and_exprt(int_min_eq, minus_one_eq)),
        "arithmetic overflow on signed division",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }
  else if(expr.id() == ID_unary_minus)
  {
    if(type.id() == ID_signedbv)
    {
      // overflow on unary- on signed integers can only happen with the
      // smallest representable number 100....0

      equal_exprt int_min_eq(
        to_unary_minus_expr(expr).op(), to_signedbv_type(type).smallest_expr());

      add_guarded_property(
        not_exprt(int_min_eq),
        "arithmetic overflow on signed unary minus",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }
    else if(type.id() == ID_unsignedbv)
    {
      // Overflow on unary- on unsigned integers happens for all operands
      // that are not zero.

      notequal_exprt not_eq_zero(
        to_unary_minus_expr(expr).op(), to_unsignedbv_type(type).zero_expr());

      add_guarded_property(
        not_eq_zero,
        "arithmetic overflow on unsigned unary minus",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }
  else if(expr.id() == ID_shl)
  {
    if(type.id() == ID_signedbv)
    {
      const auto &shl_expr = to_shl_expr(expr);
      const auto &op = shl_expr.op();
      const auto &op_type = to_signedbv_type(type);
      const auto op_width = op_type.get_width();
      const auto &distance = shl_expr.distance();
      const auto &distance_type = distance.type();

      // a left shift of a negative value is undefined;
      // yet this isn't an overflow
      exprt neg_value_shift;

      if(op_type.id() == ID_unsignedbv)
        neg_value_shift = false_exprt();
      else
        neg_value_shift =
          binary_relation_exprt(op, ID_lt, from_integer(0, op_type));

      // a shift with negative distance is undefined;
      // yet this isn't an overflow
      exprt neg_dist_shift;

      if(distance_type.id() == ID_unsignedbv)
        neg_dist_shift = false_exprt();
      else
      {
        neg_dist_shift = binary_relation_exprt(
          distance, ID_lt, from_integer(0, distance_type));
      }

      // shifting a non-zero value by more than its width is undefined;
      // yet this isn't an overflow
      const exprt dist_too_large = binary_predicate_exprt(
        distance, ID_gt, from_integer(op_width, distance_type));

      const exprt op_zero = equal_exprt(op, from_integer(0, op_type));

      auto new_type = to_bitvector_type(op_type);
      new_type.set_width(op_width * 2);

      const exprt op_ext = typecast_exprt(op, new_type);

      const exprt op_ext_shifted = shl_exprt(op_ext, distance);

      // The semantics of signed left shifts are contentious for the case
      // that a '1' is shifted into the signed bit.
      // Assuming 32-bit integers, 1<<31 is implementation-defined
      // in ANSI C and C++98, but is explicitly undefined by C99,
      // C11 and C++11.
      bool allow_shift_into_sign_bit = true;

      if(mode == ID_C)
      {
        if(
          config.ansi_c.c_standard == configt::ansi_ct::c_standardt::C99 ||
          config.ansi_c.c_standard == configt::ansi_ct::c_standardt::C11)
        {
          allow_shift_into_sign_bit = false;
        }
      }
      else if(mode == ID_cpp)
      {
        if(
          config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP11 ||
          config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP14 ||
          config.cpp.cpp_standard == configt::cppt::cpp_standardt::CPP17)
        {
          allow_shift_into_sign_bit = false;
        }
      }

      const unsigned number_of_top_bits =
        allow_shift_into_sign_bit ? op_width : op_width + 1;

      const exprt top_bits = extractbits_exprt(
        op_ext_shifted,
        new_type.get_width() - 1,
        new_type.get_width() - number_of_top_bits,
        unsignedbv_typet(number_of_top_bits));

      const exprt top_bits_zero =
        equal_exprt(top_bits, from_integer(0, top_bits.type()));

      // a negative distance shift isn't an overflow;
      // a negative value shift isn't an overflow;
      // a shift that's too far isn't an overflow;
      // a shift of zero isn't overflow;
      // else check the top bits
      add_guarded_property(
        disjunction(
          {neg_value_shift,
           neg_dist_shift,
           dist_too_large,
           op_zero,
           top_bits_zero}),
        "arithmetic overflow on signed shl",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }

  multi_ary_exprt overflow(
    "overflow-" + expr.id_string(), expr.operands(), bool_typet());

  if(expr.operands().size() >= 3)
  {
    // The overflow checks are binary!
    // We break these up.

    for(std::size_t i = 1; i < expr.operands().size(); i++)
    {
      exprt tmp;

      if(i == 1)
        tmp = to_multi_ary_expr(expr).op0();
      else
      {
        tmp = expr;
        tmp.operands().resize(i);
      }

      std::string kind = type.id() == ID_unsignedbv ? "unsigned" : "signed";

      add_guarded_property(
        not_exprt{binary_overflow_exprt{tmp, expr.id(), expr.operands()[i]}},
        "arithmetic overflow on " + kind + " " + expr.id_string(),
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }
  }
  else if(expr.operands().size() == 2)
  {
    std::string kind = type.id() == ID_unsignedbv ? "unsigned" : "signed";

    const binary_exprt &bexpr = to_binary_expr(expr);
    add_guarded_property(
      not_exprt{binary_overflow_exprt{bexpr.lhs(), expr.id(), bexpr.rhs()}},
      "arithmetic overflow on " + kind + " " + expr.id_string(),
      "overflow",
      expr.find_source_location(),
      expr,
      guard);
  }
  else
  {
    PRECONDITION(expr.id() == ID_unary_minus);

    std::string kind = type.id() == ID_unsignedbv ? "unsigned" : "signed";

    add_guarded_property(
      not_exprt{unary_minus_overflow_exprt{to_unary_expr(expr).op()}},
      "arithmetic overflow on " + kind + " " + expr.id_string(),
      "overflow",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_ct::float_overflow_check(const exprt &expr, const guardt &guard)
{
  if(!enable_float_overflow_check)
    return;

  // First, check type.
  const typet &type = expr.type();

  if(type.id() != ID_floatbv)
    return;

  // add overflow subgoal

  if(expr.id() == ID_typecast)
  {
    // Can overflow if casting from larger
    // to smaller type.
    const auto &op = to_typecast_expr(expr).op();
    if(op.type().id() == ID_floatbv)
    {
      // float-to-float
      or_exprt overflow_check{isinf_exprt(op), not_exprt(isinf_exprt(expr))};

      add_guarded_property(
        std::move(overflow_check),
        "arithmetic overflow on floating-point typecast",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }
    else
    {
      // non-float-to-float
      add_guarded_property(
        not_exprt(isinf_exprt(expr)),
        "arithmetic overflow on floating-point typecast",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }
  else if(expr.id() == ID_div)
  {
    // Can overflow if dividing by something small
    or_exprt overflow_check(
      isinf_exprt(to_div_expr(expr).dividend()), not_exprt(isinf_exprt(expr)));

    add_guarded_property(
      std::move(overflow_check),
      "arithmetic overflow on floating-point division",
      "overflow",
      expr.find_source_location(),
      expr,
      guard);

    return;
  }
  else if(expr.id() == ID_mod)
  {
    // Can't overflow
    return;
  }
  else if(expr.id() == ID_unary_minus)
  {
    // Can't overflow
    return;
  }
  else if(expr.id() == ID_plus || expr.id() == ID_mult || expr.id() == ID_minus)
  {
    if(expr.operands().size() == 2)
    {
      // Can overflow
      or_exprt overflow_check(
        isinf_exprt(to_binary_expr(expr).op0()),
        isinf_exprt(to_binary_expr(expr).op1()),
        not_exprt(isinf_exprt(expr)));

      std::string kind = expr.id() == ID_plus
                           ? "addition"
                           : expr.id() == ID_minus
                               ? "subtraction"
                               : expr.id() == ID_mult ? "multiplication" : "";

      add_guarded_property(
        std::move(overflow_check),
        "arithmetic overflow on floating-point " + kind,
        "overflow",
        expr.find_source_location(),
        expr,
        guard);

      return;
    }
    else if(expr.operands().size() >= 3)
    {
      DATA_INVARIANT(expr.id() != ID_minus, "minus expression must be binary");

      // break up
      float_overflow_check(make_binary(expr), guard);
      return;
    }
  }
}

void goto_check_ct::nan_check(const exprt &expr, const guardt &guard)
{
  if(!enable_nan_check)
    return;

  // first, check type
  if(expr.type().id() != ID_floatbv)
    return;

  if(
    expr.id() != ID_plus && expr.id() != ID_mult && expr.id() != ID_div &&
    expr.id() != ID_minus)
    return;

  // add NaN subgoal

  exprt isnan;

  if(expr.id() == ID_div)
  {
    const auto &div_expr = to_div_expr(expr);

    // there a two ways to get a new NaN on division:
    // 0/0 = NaN and x/inf = NaN
    // (note that x/0 = +-inf for x!=0 and x!=inf)
    const and_exprt zero_div_zero(
      ieee_float_equal_exprt(
        div_expr.op0(), from_integer(0, div_expr.dividend().type())),
      ieee_float_equal_exprt(
        div_expr.op1(), from_integer(0, div_expr.divisor().type())));

    const isinf_exprt div_inf(div_expr.op1());

    isnan = or_exprt(zero_div_zero, div_inf);
  }
  else if(expr.id() == ID_mult)
  {
    if(expr.operands().size() >= 3)
      return nan_check(make_binary(expr), guard);

    const auto &mult_expr = to_mult_expr(expr);

    // Inf * 0 is NaN
    const and_exprt inf_times_zero(
      isinf_exprt(mult_expr.op0()),
      ieee_float_equal_exprt(
        mult_expr.op1(), from_integer(0, mult_expr.op1().type())));

    const and_exprt zero_times_inf(
      ieee_float_equal_exprt(
        mult_expr.op1(), from_integer(0, mult_expr.op1().type())),
      isinf_exprt(mult_expr.op0()));

    isnan = or_exprt(inf_times_zero, zero_times_inf);
  }
  else if(expr.id() == ID_plus)
  {
    if(expr.operands().size() >= 3)
      return nan_check(make_binary(expr), guard);

    const auto &plus_expr = to_plus_expr(expr);

    // -inf + +inf = NaN and +inf + -inf = NaN,
    // i.e., signs differ
    ieee_float_spect spec = ieee_float_spect(to_floatbv_type(plus_expr.type()));
    exprt plus_inf = ieee_floatt::plus_infinity(spec).to_expr();
    exprt minus_inf = ieee_floatt::minus_infinity(spec).to_expr();

    isnan = or_exprt(
      and_exprt(
        equal_exprt(plus_expr.op0(), minus_inf),
        equal_exprt(plus_expr.op1(), plus_inf)),
      and_exprt(
        equal_exprt(plus_expr.op0(), plus_inf),
        equal_exprt(plus_expr.op1(), minus_inf)));
  }
  else if(expr.id() == ID_minus)
  {
    // +inf - +inf = NaN and -inf - -inf = NaN,
    // i.e., signs match

    const auto &minus_expr = to_minus_expr(expr);

    ieee_float_spect spec =
      ieee_float_spect(to_floatbv_type(minus_expr.type()));
    exprt plus_inf = ieee_floatt::plus_infinity(spec).to_expr();
    exprt minus_inf = ieee_floatt::minus_infinity(spec).to_expr();

    isnan = or_exprt(
      and_exprt(
        equal_exprt(minus_expr.lhs(), plus_inf),
        equal_exprt(minus_expr.rhs(), plus_inf)),
      and_exprt(
        equal_exprt(minus_expr.lhs(), minus_inf),
        equal_exprt(minus_expr.rhs(), minus_inf)));
  }
  else
    UNREACHABLE;

  add_guarded_property(
    boolean_negate(isnan),
    "NaN on " + expr.id_string(),
    "NaN",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_check_ct::pointer_rel_check(
  const binary_exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_check)
    return;

  if(
    expr.op0().type().id() == ID_pointer &&
    expr.op1().type().id() == ID_pointer)
  {
    // add same-object subgoal

    exprt same_object = ::same_object(expr.op0(), expr.op1());

    add_guarded_property(
      same_object,
      "same object violation",
      "pointer",
      expr.find_source_location(),
      expr,
      guard);

    for(const auto &pointer : expr.operands())
    {
      // just this particular byte must be within object bounds or one past the
      // end
      const auto size = from_integer(0, size_type());
      auto conditions = get_pointer_dereferenceable_conditions(pointer, size);

      for(const auto &c : conditions)
      {
        add_guarded_property(
          c.assertion,
          "pointer relation: " + c.description,
          "pointer arithmetic",
          expr.find_source_location(),
          pointer,
          guard);
      }
    }
  }
}

void goto_check_ct::pointer_overflow_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_overflow_check)
    return;

  if(expr.id() != ID_plus && expr.id() != ID_minus)
    return;

  DATA_INVARIANT(
    expr.operands().size() == 2,
    "pointer arithmetic expected to have exactly 2 operands");

  // multiplying the offset by the object size must not result in arithmetic
  // overflow
  const typet &object_type = to_pointer_type(expr.type()).base_type();
  if(object_type.id() != ID_empty)
  {
    auto size_of_expr_opt = size_of_expr(object_type, ns);
    CHECK_RETURN(size_of_expr_opt.has_value());
    exprt object_size = size_of_expr_opt.value();

    const binary_exprt &binary_expr = to_binary_expr(expr);
    exprt offset_operand = binary_expr.lhs().type().id() == ID_pointer
                             ? binary_expr.rhs()
                             : binary_expr.lhs();
    mult_exprt mul{
      offset_operand,
      typecast_exprt::conditional_cast(object_size, offset_operand.type())};
    mul.add_source_location() = offset_operand.source_location();

    flag_overridet override_overflow(offset_operand.source_location());
    override_overflow.set_flag(
      enable_signed_overflow_check, true, "signed_overflow_check");
    override_overflow.set_flag(
      enable_unsigned_overflow_check, true, "unsigned_overflow_check");
    integer_overflow_check(mul, guard);
  }

  // the result must be within object bounds or one past the end
  const auto size = from_integer(0, size_type());
  auto conditions = get_pointer_dereferenceable_conditions(expr, size);

  for(const auto &c : conditions)
  {
    add_guarded_property(
      c.assertion,
      "pointer arithmetic: " + c.description,
      "pointer arithmetic",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_ct::pointer_validity_check(
  const dereference_exprt &expr,
  const exprt &src_expr,
  const guardt &guard)
{
  if(!enable_pointer_check)
    return;

  const exprt &pointer = expr.pointer();

  exprt size;

  if(expr.type().id() == ID_empty)
  {
    // a dereference *p (with p being a pointer to void) is valid if p points to
    // valid memory (of any size). the smallest possible size of the memory
    // segment p could be pointing to is 1, hence we use this size for the
    // address check
    size = from_integer(1, size_type());
  }
  else
  {
    auto size_of_expr_opt = size_of_expr(expr.type(), ns);
    CHECK_RETURN(size_of_expr_opt.has_value());
    size = size_of_expr_opt.value();
  }

  auto conditions = get_pointer_dereferenceable_conditions(pointer, size);

  for(const auto &c : conditions)
  {
    add_guarded_property(
      c.assertion,
      "dereference failure: " + c.description,
      "pointer dereference",
      src_expr.find_source_location(),
      src_expr,
      guard);
  }
}

void goto_check_ct::pointer_primitive_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_primitive_check)
    return;

  if(expr.source_location().is_built_in())
    return;

  const exprt pointer =
    (expr.id() == ID_r_ok || expr.id() == ID_w_ok || expr.id() == ID_rw_ok)
      ? to_r_or_w_ok_expr(expr).pointer()
    : can_cast_expr<prophecy_r_or_w_ok_exprt>(expr)
      ? to_prophecy_r_or_w_ok_expr(expr).pointer()
      : to_unary_expr(expr).op();

  CHECK_RETURN(pointer.type().id() == ID_pointer);

  if(pointer.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(pointer);

    if(symbol_expr.get_identifier().starts_with(CPROVER_PREFIX))
      return;
  }

  const conditionst &conditions = get_pointer_points_to_valid_memory_conditions(
    pointer, from_integer(0, size_type()));
  for(const auto &c : conditions)
  {
    add_guarded_property(
      or_exprt{null_object(pointer), c.assertion},
      c.description,
      "pointer primitives",
      expr.source_location(),
      expr,
      guard);
  }
}

bool goto_check_ct::requires_pointer_primitive_check(const exprt &expr)
{
  // we don't need to include the __CPROVER_same_object primitive here as it
  // is replaced by lower level primitives in the special function handling
  // during typechecking (see c_typecheck_expr.cpp)

  // pointer_object and pointer_offset are well-defined for an arbitrary
  // pointer-typed operand (and the operands themselves have been checked
  // separately for, e.g., invalid pointer dereferencing via check_rec):
  // pointer_object and pointer_offset just extract a subset of bits from the
  // pointer. If that pointer was unconstrained (non-deterministic), the result
  // will equally be non-deterministic.
  return can_cast_expr<object_size_exprt>(expr) || expr.id() == ID_r_ok ||
         expr.id() == ID_w_ok || expr.id() == ID_rw_ok ||
         can_cast_expr<prophecy_r_or_w_ok_exprt>(expr) ||
         expr.id() == ID_is_dynamic_object;
}

goto_check_ct::conditionst
goto_check_ct::get_pointer_dereferenceable_conditions(
  const exprt &address,
  const exprt &size)
{
  auto conditions =
    get_pointer_points_to_valid_memory_conditions(address, size);
  if(auto maybe_null_condition = get_pointer_is_null_condition(address, size))
  {
    conditions.push_front(*maybe_null_condition);
  }
  return conditions;
}

std::string goto_check_ct::array_name(const exprt &expr)
{
  return ::array_name(ns, expr);
}

void goto_check_ct::bounds_check(const exprt &expr, const guardt &guard)
{
  if(!enable_bounds_check)
    return;

  if(expr.id() == ID_index)
    bounds_check_index(to_index_expr(expr), guard);
  else if(
    (expr.id() == ID_count_leading_zeros &&
     !to_count_leading_zeros_expr(expr).zero_permitted()) ||
    (expr.id() == ID_count_trailing_zeros &&
     !to_count_trailing_zeros_expr(expr).zero_permitted()))
  {
    bounds_check_bit_count(to_unary_expr(expr), guard);
  }
}

void goto_check_ct::bounds_check_index(
  const index_exprt &expr,
  const guardt &guard)
{
  const typet &array_type = expr.array().type();

  if(array_type.id() == ID_pointer)
    throw "index got pointer as array type";
  else if(array_type.id() != ID_array && array_type.id() != ID_vector)
    throw "bounds check expected array or vector type, got " +
      array_type.id_string();

  std::string name = array_name(expr.array());

  const exprt &index = expr.index();
  object_descriptor_exprt ode;
  ode.build(expr, ns);

  if(index.type().id() != ID_unsignedbv)
  {
    // we undo typecasts to signedbv
    if(
      index.id() == ID_typecast &&
      to_typecast_expr(index).op().type().id() == ID_unsignedbv)
    {
      // ok
    }
    else
    {
      const auto i = numeric_cast<mp_integer>(index);

      if(!i.has_value() || *i < 0)
      {
        exprt effective_offset = ode.offset();

        if(ode.root_object().id() == ID_dereference)
        {
          exprt p_offset =
            pointer_offset(to_dereference_expr(ode.root_object()).pointer());

          effective_offset = plus_exprt{
            p_offset,
            typecast_exprt::conditional_cast(
              effective_offset, p_offset.type())};
        }

        exprt zero = from_integer(0, effective_offset.type());

        // the final offset must not be negative
        binary_relation_exprt inequality(
          effective_offset, ID_ge, std::move(zero));

        add_guarded_property(
          inequality,
          name + " lower bound",
          "array bounds",
          expr.find_source_location(),
          expr,
          guard);
      }
    }
  }

  if(ode.root_object().id() == ID_dereference)
  {
    const exprt &pointer = to_dereference_expr(ode.root_object()).pointer();

    const plus_exprt effective_offset{
      ode.offset(),
      typecast_exprt::conditional_cast(
        pointer_offset(pointer), ode.offset().type())};

    binary_relation_exprt inequality{
      effective_offset,
      ID_lt,
      typecast_exprt::conditional_cast(
        object_size(pointer), effective_offset.type())};

    exprt in_bounds_of_some_explicit_allocation =
      is_in_bounds_of_some_explicit_allocation(
        pointer,
        plus_exprt{ode.offset(), from_integer(1, ode.offset().type())});

    or_exprt precond(
      std::move(in_bounds_of_some_explicit_allocation), inequality);

    add_guarded_property(
      precond,
      name + " dynamic object upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);

    return;
  }

  const exprt &size = array_type.id() == ID_array
                        ? to_array_type(array_type).size()
                        : to_vector_type(array_type).size();

  if(size.is_nil() && !array_type.get_bool(ID_C_flexible_array_member))
  {
    // Linking didn't complete, we don't have a size.
    // Not clear what to do.
  }
  else if(size.id() == ID_infinity)
  {
  }
  else if(
    expr.array().id() == ID_member &&
    (size.is_zero() || array_type.get_bool(ID_C_flexible_array_member)))
  {
    // a variable sized struct member
    //
    // Excerpt from the C standard on flexible array members:
    // However, when a . (or ->) operator has a left operand that is (a pointer
    // to) a structure with a flexible array member and the right operand names
    // that member, it behaves as if that member were replaced with the longest
    // array (with the same element type) that would not make the structure
    // larger than the object being accessed; [...]
    const auto type_size_opt =
      pointer_offset_size(ode.root_object().type(), ns);
    CHECK_RETURN(type_size_opt.has_value());

    binary_relation_exprt inequality(
      ode.offset(),
      ID_lt,
      from_integer(type_size_opt.value(), ode.offset().type()));

    add_guarded_property(
      inequality,
      name + " upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);
  }
  else
  {
    binary_relation_exprt inequality{
      typecast_exprt::conditional_cast(index, size.type()), ID_lt, size};

    add_guarded_property(
      inequality,
      name + " upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_ct::bounds_check_bit_count(
  const unary_exprt &expr,
  const guardt &guard)
{
  std::string name;

  if(expr.id() == ID_count_leading_zeros)
    name = "leading";
  else if(expr.id() == ID_count_trailing_zeros)
    name = "trailing";
  else
    PRECONDITION(false);

  add_guarded_property(
    notequal_exprt{expr.op(), from_integer(0, expr.op().type())},
    "count " + name + " zeros is undefined for value zero",
    "bit count",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_check_ct::add_guarded_property(
  const exprt &asserted_expr,
  const std::string &comment,
  const std::string &property_class,
  const source_locationt &source_location,
  const exprt &src_expr,
  const guardt &guard)
{
  // first try simplifier on it
  exprt simplified_expr =
    enable_simplify ? simplify_expr(asserted_expr, ns) : asserted_expr;

  // throw away trivial properties?
  if(!retain_trivial && simplified_expr.is_true())
    return;

  // add the guard
  exprt guarded_expr = guard(simplified_expr);

  if(assertions.insert(std::make_pair(src_expr, guarded_expr)).second)
  {
    std::string source_expr_string;
    get_language_from_mode(mode)->from_expr(src_expr, source_expr_string, ns);

    source_locationt annotated_location = source_location;
    annotated_location.set_comment(comment + " in " + source_expr_string);
    annotated_location.set_property_class(property_class);

    add_all_checked_named_check_pragmas(annotated_location);

    if(enable_assert_to_assume)
    {
      new_code.add(goto_programt::make_assumption(
        std::move(guarded_expr), annotated_location));
    }
    else
    {
      new_code.add(goto_programt::make_assertion(
        std::move(guarded_expr), annotated_location));
    }
  }
}

void goto_check_ct::check_rec_address(const exprt &expr, const guardt &guard)
{
  // we don't look into quantifiers
  if(expr.id() == ID_exists || expr.id() == ID_forall)
    return;

  if(expr.id() == ID_dereference)
  {
    check_rec(to_dereference_expr(expr).pointer(), guard);
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);
    check_rec_address(index_expr.array(), guard);
    check_rec(index_expr.index(), guard);
  }
  else
  {
    for(const auto &operand : expr.operands())
      check_rec_address(operand, guard);
  }
}

void goto_check_ct::check_rec_logical_op(const exprt &expr, const guardt &guard)
{
  PRECONDITION(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies);
  INVARIANT(
    expr.is_boolean(),
    "'" + expr.id_string() + "' must be Boolean, but got " + expr.pretty());

  exprt::operandst constraints;

  for(const auto &op : expr.operands())
  {
    INVARIANT(
      op.is_boolean(),
      "'" + expr.id_string() + "' takes Boolean operands only, but got " +
        op.pretty());

    auto new_guard = [&guard, &constraints](exprt expr) {
      return guard(implication(conjunction(constraints), expr));
    };

    check_rec(op, new_guard);

    constraints.push_back(expr.id() == ID_or ? boolean_negate(op) : op);
  }
}

void goto_check_ct::check_rec_if(const if_exprt &if_expr, const guardt &guard)
{
  INVARIANT(
    if_expr.cond().is_boolean(),
    "first argument of if must be boolean, but got " + if_expr.cond().pretty());

  check_rec(if_expr.cond(), guard);

  {
    auto new_guard = [&guard, &if_expr](exprt expr) {
      return guard(implication(if_expr.cond(), std::move(expr)));
    };
    check_rec(if_expr.true_case(), new_guard);
  }

  {
    auto new_guard = [&guard, &if_expr](exprt expr) {
      return guard(implication(not_exprt(if_expr.cond()), std::move(expr)));
    };
    check_rec(if_expr.false_case(), new_guard);
  }
}

bool goto_check_ct::check_rec_member(
  const member_exprt &member,
  const guardt &guard)
{
  const dereference_exprt &deref = to_dereference_expr(member.struct_op());

  check_rec(deref.pointer(), guard);

  // avoid building the following expressions when pointer_validity_check
  // would return immediately anyway
  if(!enable_pointer_check)
    return true;

  // we rewrite s->member into *(s+member_offset)
  // to avoid requiring memory safety of the entire struct
  auto member_offset_opt = member_offset_expr(member, ns);

  if(member_offset_opt.has_value())
  {
    pointer_typet new_pointer_type = to_pointer_type(deref.pointer().type());
    new_pointer_type.base_type() = member.type();

    const exprt char_pointer = typecast_exprt::conditional_cast(
      deref.pointer(), pointer_type(char_type()));

    const exprt new_address_casted = typecast_exprt::conditional_cast(
      plus_exprt{
        char_pointer,
        typecast_exprt::conditional_cast(
          member_offset_opt.value(), pointer_diff_type())},
      new_pointer_type);

    dereference_exprt new_deref{new_address_casted};
    new_deref.add_source_location() = deref.source_location();
    pointer_validity_check(new_deref, member, guard);

    return true;
  }
  return false;
}

void goto_check_ct::check_rec_div(
  const div_exprt &div_expr,
  const guardt &guard)
{
  if(
    div_expr.type().id() == ID_signedbv ||
    div_expr.type().id() == ID_unsignedbv || div_expr.type().id() == ID_c_bool)
  {
    // Division by zero is undefined behavior for all integer types.
    div_by_zero_check(to_div_expr(div_expr), guard);
  }
  else if(div_expr.type().id() == ID_floatbv)
  {
    // Division by zero on floating-point numbers may be undefined behavior.
    // Annex F of the ISO C21 suggests that implementations that
    // define __STDC_IEC_559__ follow IEEE 754 semantics,
    // which defines the outcome of division by zero.
    float_div_by_zero_check(to_div_expr(div_expr), guard);
  }

  if(div_expr.type().id() == ID_signedbv)
    integer_overflow_check(div_expr, guard);
  else if(div_expr.type().id() == ID_floatbv)
  {
    nan_check(div_expr, guard);
    float_overflow_check(div_expr, guard);
  }
}

void goto_check_ct::check_rec_arithmetic_op(
  const exprt &expr,
  const guardt &guard)
{
  if(expr.type().id() == ID_signedbv || expr.type().id() == ID_unsignedbv)
  {
    integer_overflow_check(expr, guard);

    if(
      expr.operands().size() == 2 && expr.id() == ID_minus &&
      expr.operands()[0].type().id() == ID_pointer &&
      expr.operands()[1].type().id() == ID_pointer)
    {
      pointer_rel_check(to_binary_expr(expr), guard);
    }
  }
  else if(expr.type().id() == ID_floatbv)
  {
    nan_check(expr, guard);
    float_overflow_check(expr, guard);
  }
  else if(expr.type().id() == ID_pointer)
  {
    pointer_overflow_check(expr, guard);
  }
}

void goto_check_ct::check_rec(const exprt &expr, const guardt &guard)
{
  if(expr.id() == ID_exists || expr.id() == ID_forall)
  {
    // the scoped variables may be used in the assertion
    const auto &quantifier_expr = to_quantifier_expr(expr);

    auto new_guard = [&guard, &quantifier_expr](exprt expr) {
      return guard(forall_exprt(quantifier_expr.symbol(), expr));
    };

    check_rec(quantifier_expr.where(), new_guard);
    return;
  }
  else if(expr.id() == ID_address_of)
  {
    check_rec_address(to_address_of_expr(expr).object(), guard);
    return;
  }
  else if(expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies)
  {
    check_rec_logical_op(expr, guard);
    return;
  }
  else if(expr.id() == ID_if)
  {
    check_rec_if(to_if_expr(expr), guard);
    return;
  }
  else if(
    expr.id() == ID_member &&
    to_member_expr(expr).struct_op().id() == ID_dereference)
  {
    if(check_rec_member(to_member_expr(expr), guard))
      return;
  }

  for(const auto &op : expr.operands())
    check_rec(op, guard);

  if(expr.type().id() == ID_c_enum_tag)
    enum_range_check(expr, guard);

  if(expr.id() == ID_index)
  {
    bounds_check(expr, guard);
  }
  else if(expr.id() == ID_div)
  {
    check_rec_div(to_div_expr(expr), guard);
  }
  else if(expr.id() == ID_shl || expr.id() == ID_ashr || expr.id() == ID_lshr)
  {
    undefined_shift_check(to_shift_expr(expr), guard);

    if(expr.id() == ID_shl && expr.type().id() == ID_signedbv)
      integer_overflow_check(expr, guard);
  }
  else if(expr.id() == ID_mod)
  {
    mod_by_zero_check(to_mod_expr(expr), guard);
    mod_overflow_check(to_mod_expr(expr), guard);
  }
  else if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
    expr.id() == ID_unary_minus)
  {
    check_rec_arithmetic_op(expr, guard);
  }
  else if(expr.id() == ID_typecast)
    conversion_check(expr, guard);
  else if(
    expr.id() == ID_le || expr.id() == ID_lt || expr.id() == ID_ge ||
    expr.id() == ID_gt)
    pointer_rel_check(to_binary_relation_expr(expr), guard);
  else if(expr.id() == ID_dereference)
  {
    pointer_validity_check(to_dereference_expr(expr), expr, guard);
  }
  else if(requires_pointer_primitive_check(expr))
  {
    pointer_primitive_check(expr, guard);
  }
  else if(
    expr.id() == ID_count_leading_zeros || expr.id() == ID_count_trailing_zeros)
  {
    bounds_check(expr, guard);
  }
}

void goto_check_ct::check(const exprt &expr)
{
  check_rec(expr, identity);
}

void goto_check_ct::memory_leak_check(const irep_idt &function_id)
{
  const symbolt &leak = ns.lookup(CPROVER_PREFIX "memory_leak");
  const symbol_exprt leak_expr = leak.symbol_expr();

  // add self-assignment to get helpful counterexample output
  new_code.add(goto_programt::make_assignment(leak_expr, leak_expr));

  source_locationt source_location;
  source_location.set_function(function_id);

  equal_exprt eq(leak_expr, null_pointer_exprt(to_pointer_type(leak.type)));

  add_guarded_property(
    eq,
    "dynamically allocated memory never freed",
    "memory-leak",
    source_location,
    eq,
    identity);
}

void goto_check_ct::goto_check(
  const irep_idt &function_identifier,
  goto_functiont &goto_function)
{
  const auto &function_symbol = ns.lookup(function_identifier);
  mode = function_symbol.mode;

  if(mode != ID_C && mode != ID_cpp)
    return;

  assertions.clear();

  bool did_something = false;

  local_bitvector_analysis =
    std::make_unique<local_bitvector_analysist>(goto_function, ns);

  goto_programt &goto_program = goto_function.body;

  Forall_goto_program_instructions(it, goto_program)
  {
    current_target = it;
    goto_programt::instructiont &i = *it;

    flag_overridet resetter(i.source_location());
    const auto &pragmas = i.source_location().get_pragmas();
    for(const auto &d : pragmas)
    {
      // match named-check related pragmas
      auto matched = match_named_check(d.first);
      if(matched.has_value())
      {
        auto named_check = matched.value();
        auto name = named_check.first;
        auto status = named_check.second;
        bool *flag = name_to_flag.find(name)->second;
        switch(status)
        {
        case check_statust::ENABLE:
          resetter.set_flag(*flag, true, name);
          break;
        case check_statust::DISABLE:
          resetter.set_flag(*flag, false, name);
          break;
        case check_statust::CHECKED:
          resetter.disable_flag(*flag, name);
          break;
        }
      }
    }

    // add checked pragmas for all active checks
    add_active_named_check_pragmas(i.source_location_nonconst());

    new_code.clear();

    // we clear all recorded assertions if
    // 1) we want to generate all assertions or
    // 2) the instruction is a branch target
    if(retain_trivial || i.is_target())
      assertions.clear();

    if(i.has_condition())
    {
      check(i.condition());
    }

    // magic ERROR label?
    for(const auto &label : error_labels)
    {
      if(std::find(i.labels.begin(), i.labels.end(), label) != i.labels.end())
      {
        source_locationt annotated_location = i.source_location();
        annotated_location.set_property_class("error label");
        annotated_location.set_comment("error label " + label);
        annotated_location.set("user-provided", true);

        if(enable_assert_to_assume)
        {
          new_code.add(
            goto_programt::make_assumption(false_exprt{}, annotated_location));
        }
        else
        {
          new_code.add(
            goto_programt::make_assertion(false_exprt{}, annotated_location));
        }
      }
    }

    if(i.is_other())
    {
      const auto &code = i.get_other();
      const irep_idt &statement = code.get_statement();

      if(statement == ID_expression)
      {
        check(code);
      }
      else if(statement == ID_printf)
      {
        for(const auto &op : code.operands())
          check(op);
      }
    }
    else if(i.is_assign())
    {
      const exprt &assign_lhs = i.assign_lhs();
      const exprt &assign_rhs = i.assign_rhs();

      // Disable enum range checks for left-hand sides as their values are yet
      // to be set (by this assignment).
      {
        flag_overridet resetter(i.source_location());
        resetter.disable_flag(enable_enum_range_check, "enum_range_check");
        check(assign_lhs);
      }

      check(assign_rhs);

      // the LHS might invalidate any assertion
      invalidate(assign_lhs);
    }
    else if(i.is_function_call())
    {
      // Disable enum range checks for left-hand sides as their values are yet
      // to be set (by this function call).
      {
        flag_overridet resetter(i.source_location());
        resetter.disable_flag(enable_enum_range_check, "enum_range_check");
        check(i.call_lhs());
      }
      check(i.call_function());

      for(const auto &arg : i.call_arguments())
        check(arg);

      check_shadow_memory_api_calls(i);

      // the call might invalidate any assertion
      assertions.clear();
    }
    else if(i.is_set_return_value())
    {
      check(i.return_value());
      // the return value invalidate any assertion
      invalidate(i.return_value());
    }
    else if(i.is_throw())
    {
      // this has no successor
      assertions.clear();
    }
    else if(i.is_assume())
    {
      // These are further 'exit points' of the program
      const exprt simplified_guard = simplify_expr(i.condition(), ns);
      if(
        enable_memory_cleanup_check && simplified_guard.is_false() &&
        (function_identifier == "abort" || function_identifier == "exit" ||
         function_identifier == "_Exit" ||
         (i.labels.size() == 1 && i.labels.front() == "__VERIFIER_abort")))
      {
        memory_leak_check(function_identifier);
      }
    }
    else if(i.is_dead())
    {
      if(enable_pointer_check || enable_pointer_primitive_check)
      {
        const symbol_exprt &variable = i.dead_symbol();

        // is it dirty?
        if(local_bitvector_analysis->dirty(variable))
        {
          // need to mark the dead variable as dead
          exprt lhs = ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr();
          exprt address_of_expr = typecast_exprt::conditional_cast(
            address_of_exprt(variable), lhs.type());
          if_exprt rhs(
            side_effect_expr_nondett(bool_typet(), i.source_location()),
            std::move(address_of_expr),
            lhs);
          new_code.add(goto_programt::make_assignment(
            code_assignt{std::move(lhs), std::move(rhs), i.source_location()},
            i.source_location()));
        }
      }
    }
    else if(i.is_end_function())
    {
      if(
        function_identifier == goto_functionst::entry_point() &&
        enable_memory_leak_check)
      {
        memory_leak_check(function_identifier);
      }
    }

    for(auto &instruction : new_code.instructions)
    {
      if(instruction.source_location().is_nil())
      {
        instruction.source_location_nonconst().id(irep_idt());

        if(!it->source_location().get_file().empty())
          instruction.source_location_nonconst().set_file(
            it->source_location().get_file());

        if(!it->source_location().get_line().empty())
          instruction.source_location_nonconst().set_line(
            it->source_location().get_line());

        if(!it->source_location().get_function().empty())
          instruction.source_location_nonconst().set_function(
            it->source_location().get_function());

        if(!it->source_location().get_column().empty())
        {
          instruction.source_location_nonconst().set_column(
            it->source_location().get_column());
        }
      }
    }

    // insert new instructions -- make sure targets are not moved
    did_something |= !new_code.instructions.empty();

    while(!new_code.instructions.empty())
    {
      goto_program.insert_before_swap(it, new_code.instructions.front());
      new_code.instructions.pop_front();
      it++;
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

void goto_check_ct::check_shadow_memory_api_calls(
  const goto_programt::instructiont &i)
{
  if(i.call_function().id() != ID_symbol)
    return;

  const irep_idt &identifier =
    to_symbol_expr(i.call_function()).get_identifier();

  if(
    identifier == CPROVER_PREFIX "get_field" || identifier == CPROVER_PREFIX
                                                  "set_field")
  {
    const exprt &expr = i.call_arguments()[0];
    PRECONDITION(expr.type().id() == ID_pointer);
    check(dereference_exprt(expr));
  }
}

goto_check_ct::conditionst
goto_check_ct::get_pointer_points_to_valid_memory_conditions(
  const exprt &address,
  const exprt &size)
{
  PRECONDITION(local_bitvector_analysis);
  PRECONDITION(address.type().id() == ID_pointer);
  local_bitvector_analysist::flagst flags =
    local_bitvector_analysis->get(current_target, address);

  conditionst conditions;

  const exprt in_bounds_of_some_explicit_allocation =
    is_in_bounds_of_some_explicit_allocation(address, size);

  const bool unknown = flags.is_unknown() || flags.is_uninitialized();

  if(unknown)
  {
    conditions.push_back(conditiont{
      not_exprt{is_invalid_pointer_exprt{address}}, "pointer invalid"});
  }

  if(unknown || flags.is_dynamic_heap())
  {
    conditions.push_back(conditiont(
      or_exprt(
        in_bounds_of_some_explicit_allocation,
        not_exprt(deallocated(address, ns))),
      "deallocated dynamic object"));
  }

  if(unknown || flags.is_dynamic_local())
  {
    conditions.push_back(conditiont(
      or_exprt(
        in_bounds_of_some_explicit_allocation,
        not_exprt(dead_object(address, ns))),
      "dead object"));
  }

  if(flags.is_dynamic_heap())
  {
    const or_exprt object_bounds_violation(
      object_lower_bound(address, nil_exprt()),
      object_upper_bound(address, size));

    conditions.push_back(conditiont(
      or_exprt(
        in_bounds_of_some_explicit_allocation,
        not_exprt(object_bounds_violation)),
      "pointer outside dynamic object bounds"));
  }

  if(unknown || flags.is_dynamic_local() || flags.is_static_lifetime())
  {
    const or_exprt object_bounds_violation(
      object_lower_bound(address, nil_exprt()),
      object_upper_bound(address, size));

    conditions.push_back(conditiont(
      or_exprt(
        in_bounds_of_some_explicit_allocation,
        not_exprt(object_bounds_violation)),
      "pointer outside object bounds"));
  }

  if(unknown || flags.is_integer_address())
  {
    conditions.push_back(conditiont(
      implies_exprt(
        integer_address(address), in_bounds_of_some_explicit_allocation),
      "invalid integer address"));
  }

  return conditions;
}

std::optional<goto_check_ct::conditiont>
goto_check_ct::get_pointer_is_null_condition(
  const exprt &address,
  const exprt &size)
{
  PRECONDITION(local_bitvector_analysis);
  PRECONDITION(address.type().id() == ID_pointer);
  local_bitvector_analysist::flagst flags =
    local_bitvector_analysis->get(current_target, address);

  if(flags.is_unknown() || flags.is_uninitialized() || flags.is_null())
  {
    return {conditiont{
      or_exprt{
        is_in_bounds_of_some_explicit_allocation(address, size),
        not_exprt(null_object(address))},
      "pointer NULL"}};
  }

  return {};
}

exprt goto_check_ct::is_in_bounds_of_some_explicit_allocation(
  const exprt &pointer,
  const exprt &size)
{
  exprt::operandst alloc_disjuncts;
  for(const auto &a : allocations)
  {
    typecast_exprt int_ptr(pointer, a.first.type());

    binary_relation_exprt lb_check(a.first, ID_le, int_ptr);

    plus_exprt upper_bound{
      int_ptr, typecast_exprt::conditional_cast(size, int_ptr.type())};

    binary_relation_exprt ub_check{
      std::move(upper_bound), ID_le, plus_exprt{a.first, a.second}};

    alloc_disjuncts.push_back(
      and_exprt{std::move(lb_check), std::move(ub_check)});
  }
  return disjunction(alloc_disjuncts);
}

void goto_check_c(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options,
  message_handlert &message_handler)
{
  goto_check_ct goto_check(ns, options, message_handler);
  goto_check.goto_check(function_identifier, goto_function);
}

void goto_check_c(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  goto_check_ct goto_check(ns, options, message_handler);

  goto_check.collect_allocations(goto_functions);

  for(auto &gf_entry : goto_functions.function_map)
  {
    goto_check.goto_check(gf_entry.first, gf_entry.second);
  }
}

void goto_check_c(
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  goto_check_c(ns, options, goto_model.goto_functions, message_handler);
}

void goto_check_ct::add_active_named_check_pragmas(
  source_locationt &source_location) const
{
  for(const auto &entry : name_to_flag)
    if(*(entry.second))
      source_location.add_pragma("checked:" + id2string(entry.first));
}

void goto_check_ct::add_all_checked_named_check_pragmas(
  source_locationt &source_location) const
{
  for(const auto &entry : name_to_flag)
    source_location.add_pragma("checked:" + id2string(entry.first));
}

goto_check_ct::named_check_statust
goto_check_ct::match_named_check(const irep_idt &named_check) const
{
  auto s = id2string(named_check);
  auto col = s.find(":");

  if(col == std::string::npos)
    return {}; // separator not found

  auto name = s.substr(col + 1);

  if(name_to_flag.find(name) == name_to_flag.end())
    return {}; // name unknown

  check_statust status;
  if(!s.compare(0, 6, "enable"))
    status = check_statust::ENABLE;
  else if(!s.compare(0, 7, "disable"))
    status = check_statust::DISABLE;
  else if(!s.compare(0, 7, "checked"))
    status = check_statust::CHECKED;
  else
    return {}; // prefix unknow

  // success
  return std::pair<irep_idt, check_statust>{name, status};
}
