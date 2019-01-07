/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/array_name.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/guard.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/options.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <goto-programs/remove_skip.h>

#include "local_bitvector_analysis.h"

class goto_checkt
{
public:
  goto_checkt(
    const namespacet &_ns,
    const optionst &_options):
    ns(_ns),
    local_bitvector_analysis(nullptr)
  {
    enable_bounds_check=_options.get_bool_option("bounds-check");
    enable_pointer_check=_options.get_bool_option("pointer-check");
    enable_memory_leak_check=_options.get_bool_option("memory-leak-check");
    enable_div_by_zero_check=_options.get_bool_option("div-by-zero-check");
    enable_signed_overflow_check=
      _options.get_bool_option("signed-overflow-check");
    enable_unsigned_overflow_check=
      _options.get_bool_option("unsigned-overflow-check");
    enable_pointer_overflow_check=
      _options.get_bool_option("pointer-overflow-check");
    enable_conversion_check=_options.get_bool_option("conversion-check");
    enable_undefined_shift_check=
      _options.get_bool_option("undefined-shift-check");
    enable_float_overflow_check=
      _options.get_bool_option("float-overflow-check");
    enable_simplify=_options.get_bool_option("simplify");
    enable_nan_check=_options.get_bool_option("nan-check");
    retain_trivial=_options.get_bool_option("retain-trivial");
    enable_assert_to_assume=_options.get_bool_option("assert-to-assume");
    enable_assertions=_options.get_bool_option("assertions");
    enable_built_in_assertions=_options.get_bool_option("built-in-assertions");
    enable_assumptions=_options.get_bool_option("assumptions");
    error_labels=_options.get_list_option("error-label");
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  void goto_check(goto_functiont &goto_function, const irep_idt &mode);

  void collect_allocations(const goto_functionst &goto_functions);

protected:
  const namespacet &ns;
  std::unique_ptr<local_bitvector_analysist> local_bitvector_analysis;
  goto_programt::const_targett current_target;

  void check_rec(
    const exprt &expr,
    guardt &guard,
    bool address);
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

  void bounds_check(const index_exprt &, const guardt &);
  void div_by_zero_check(const div_exprt &, const guardt &);
  void mod_by_zero_check(const mod_exprt &, const guardt &);
  void mod_overflow_check(const mod_exprt &, const guardt &);
  void undefined_shift_check(const shift_exprt &, const guardt &);
  void pointer_rel_check(const exprt &, const guardt &);
  void pointer_overflow_check(const exprt &, const guardt &);
  void pointer_validity_check(const dereference_exprt &, const guardt &);
  conditionst address_check(const exprt &address, const exprt &size);
  void integer_overflow_check(const exprt &, const guardt &);
  void conversion_check(const exprt &, const guardt &);
  void float_overflow_check(const exprt &, const guardt &);
  void nan_check(const exprt &, const guardt &);
  void rw_ok_check(exprt &);

  std::string array_name(const exprt &);

  void add_guarded_claim(
    const exprt &expr,
    const std::string &comment,
    const std::string &property_class,
    const source_locationt &,
    const exprt &src_expr,
    const guardt &guard);

  goto_programt new_code;
  typedef std::set<exprt> assertionst;
  assertionst assertions;

  void invalidate(const exprt &lhs);

  bool enable_bounds_check;
  bool enable_pointer_check;
  bool enable_memory_leak_check;
  bool enable_div_by_zero_check;
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
  bool enable_assertions;
  bool enable_built_in_assertions;
  bool enable_assumptions;

  typedef optionst::value_listt error_labelst;
  error_labelst error_labels;

  // the first element of the pair is the base address,
  // and the second is the size of the region
  typedef std::pair<exprt, exprt> allocationt;
  typedef std::list<allocationt> allocationst;
  allocationst allocations;

  irep_idt mode;
};

void goto_checkt::collect_allocations(
  const goto_functionst &goto_functions)
{
  if(!enable_pointer_check)
    return;

  forall_goto_functions(itf, goto_functions)
    forall_goto_program_instructions(it, itf->second.body)
    {
      const goto_programt::instructiont &instruction=*it;
      if(!instruction.is_function_call())
        continue;

      const code_function_callt &call=
        to_code_function_call(instruction.code);
      if(call.function().id()!=ID_symbol ||
         to_symbol_expr(call.function()).get_identifier()!=
         CPROVER_PREFIX "allocated_memory")
        continue;

      const code_function_callt::argumentst &args= call.arguments();
      if(args.size()!=2 ||
         args[0].type().id()!=ID_unsignedbv ||
         args[1].type().id()!=ID_unsignedbv)
        throw "expected two unsigned arguments to "
              CPROVER_PREFIX "allocated_memory";

      assert(args[0].type()==args[1].type());
      allocations.push_back({args[0], args[1]});
    }
}

void goto_checkt::invalidate(const exprt &lhs)
{
  if(lhs.id()==ID_index)
    invalidate(to_index_expr(lhs).array());
  else if(lhs.id()==ID_member)
    invalidate(to_member_expr(lhs).struct_op());
  else if(lhs.id()==ID_symbol)
  {
    // clear all assertions about 'symbol'
    find_symbols_sett find_symbols_set;
    find_symbols_set.insert(to_symbol_expr(lhs).get_identifier());

    for(assertionst::iterator
        it=assertions.begin();
        it!=assertions.end();
        ) // no it++
    {
      assertionst::iterator next=it;
      next++;

      if(has_symbol(*it, find_symbols_set) || has_subexpr(*it, ID_dereference))
        assertions.erase(it);

      it=next;
    }
  }
  else
  {
    // give up, clear all
    assertions.clear();
  }
}

void goto_checkt::div_by_zero_check(
  const div_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero=from_integer(0, expr.op1().type());

  if(zero.is_nil())
    throw "no zero of argument type of operator "+expr.id_string();

  const notequal_exprt inequality(expr.op1(), zero);

  add_guarded_claim(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_checkt::undefined_shift_check(
  const shift_exprt &expr,
  const guardt &guard)
{
  if(!enable_undefined_shift_check)
    return;

  // Undefined for all types and shifts if distance exceeds width,
  // and also undefined for negative distances.

  const typet &distance_type=
    ns.follow(expr.distance().type());

  if(distance_type.id()==ID_signedbv)
  {
    binary_relation_exprt inequality(
      expr.distance(), ID_ge, from_integer(0, distance_type));

    add_guarded_claim(
      inequality,
      "shift distance is negative",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);
  }

  const typet &op_type=
    ns.follow(expr.op().type());

  if(op_type.id()==ID_unsignedbv || op_type.id()==ID_signedbv)
  {
    exprt width_expr=
      from_integer(to_bitvector_type(op_type).get_width(), distance_type);

    if(width_expr.is_nil())
      throw "no number for width for operator "+expr.id_string();

    add_guarded_claim(
      binary_relation_exprt(expr.distance(), ID_lt, width_expr),
      "shift distance too large",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);

    if(op_type.id()==ID_signedbv && expr.id()==ID_shl)
    {
      binary_relation_exprt inequality(
        expr.op(), ID_ge, from_integer(0, op_type));

      add_guarded_claim(
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
    add_guarded_claim(
      false_exprt(),
      "shift of non-integer type",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_checkt::mod_by_zero_check(
  const mod_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check || mode == ID_java)
    return;

  // add divison by zero subgoal

  exprt zero=from_integer(0, expr.op1().type());

  if(zero.is_nil())
    throw "no zero of argument type of operator "+expr.id_string();

  const notequal_exprt inequality(expr.op1(), zero);

  add_guarded_claim(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

/// check a mod expression for the case INT_MIN % -1
void goto_checkt::mod_overflow_check(const mod_exprt &expr, const guardt &guard)
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

    add_guarded_claim(
      or_exprt(int_min_neq, minus_one_neq),
      "result of signed mod is not representable",
      "overflow",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_checkt::conversion_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_conversion_check)
    return;

  // First, check type.
  const typet &type=ns.follow(expr.type());

  if(type.id()!=ID_signedbv &&
     type.id()!=ID_unsignedbv)
    return;

  if(expr.id()==ID_typecast)
  {
    // conversion to signed int may overflow

    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    const typet &old_type=ns.follow(expr.op0().type());

    if(type.id()==ID_signedbv)
    {
      std::size_t new_width=to_signedbv_type(type).get_width();

      if(old_type.id()==ID_signedbv) // signed -> signed
      {
        std::size_t old_width=to_signedbv_type(old_type).get_width();
        if(new_width>=old_width)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          expr.op0(),
          ID_le,
          from_integer(power(2, new_width - 1) - 1, old_type));

        const binary_relation_exprt no_overflow_lower(
          expr.op0(), ID_ge, from_integer(-power(2, new_width - 1), old_type));

        add_guarded_claim(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on signed type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id()==ID_unsignedbv) // unsigned -> signed
      {
        std::size_t old_width=to_unsignedbv_type(old_type).get_width();
        if(new_width>=old_width+1)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          expr.op0(),
          ID_le,
          from_integer(power(2, new_width - 1) - 1, old_type));

        add_guarded_claim(
          no_overflow_upper,
          "arithmetic overflow on unsigned to signed type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id()==ID_floatbv) // float -> signed
      {
        // Note that the fractional part is truncated!
        ieee_floatt upper(to_floatbv_type(old_type));
        upper.from_integer(power(2, new_width-1));
        const binary_relation_exprt no_overflow_upper(
          expr.op0(), ID_lt, upper.to_expr());

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-power(2, new_width-1)-1);
        const binary_relation_exprt no_overflow_lower(
          expr.op0(), ID_gt, lower.to_expr());

        add_guarded_claim(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on float to signed integer type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
    }
    else if(type.id()==ID_unsignedbv)
    {
      std::size_t new_width=to_unsignedbv_type(type).get_width();

      if(old_type.id()==ID_signedbv) // signed -> unsigned
      {
        std::size_t old_width=to_signedbv_type(old_type).get_width();

        if(new_width>=old_width-1)
        {
          // only need lower bound check
          const binary_relation_exprt no_overflow_lower(
            expr.op0(), ID_ge, from_integer(0, old_type));

          add_guarded_claim(
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
            expr.op0(), ID_le, from_integer(power(2, new_width) - 1, old_type));

          const binary_relation_exprt no_overflow_lower(
            expr.op0(), ID_ge, from_integer(0, old_type));

          add_guarded_claim(
            and_exprt(no_overflow_lower, no_overflow_upper),
            "arithmetic overflow on signed to unsigned type conversion",
            "overflow",
            expr.find_source_location(),
            expr,
            guard);
        }
      }
      else if(old_type.id()==ID_unsignedbv) // unsigned -> unsigned
      {
        std::size_t old_width=to_unsignedbv_type(old_type).get_width();
        if(new_width>=old_width)
          return; // always ok

        const binary_relation_exprt no_overflow_upper(
          expr.op0(), ID_le, from_integer(power(2, new_width) - 1, old_type));

        add_guarded_claim(
          no_overflow_upper,
          "arithmetic overflow on unsigned to unsigned type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
      else if(old_type.id()==ID_floatbv) // float -> unsigned
      {
        // Note that the fractional part is truncated!
        ieee_floatt upper(to_floatbv_type(old_type));
        upper.from_integer(power(2, new_width)-1);
        const binary_relation_exprt no_overflow_upper(
          expr.op0(), ID_lt, upper.to_expr());

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-1);
        const binary_relation_exprt no_overflow_lower(
          expr.op0(), ID_gt, lower.to_expr());

        add_guarded_claim(
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

void goto_checkt::integer_overflow_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_signed_overflow_check &&
     !enable_unsigned_overflow_check)
    return;

  // First, check type.
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_signedbv && !enable_signed_overflow_check)
    return;

  if(type.id()==ID_unsignedbv && !enable_unsigned_overflow_check)
    return;

  // add overflow subgoal

  if(expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);

    // undefined for signed division INT_MIN/-1
    if(type.id()==ID_signedbv)
    {
      equal_exprt int_min_eq(
        expr.op0(), to_signedbv_type(type).smallest_expr());

      equal_exprt minus_one_eq(
        expr.op1(), from_integer(-1, type));

      add_guarded_claim(
        not_exprt(and_exprt(int_min_eq, minus_one_eq)),
        "arithmetic overflow on signed division",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }
  else if(expr.id()==ID_unary_minus)
  {
    if(type.id()==ID_signedbv)
    {
      // overflow on unary- can only happen with the smallest
      // representable number 100....0

      equal_exprt int_min_eq(
        expr.op0(), to_signedbv_type(type).smallest_expr());

      add_guarded_claim(
        not_exprt(int_min_eq),
        "arithmetic overflow on signed unary minus",
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
        neg_dist_shift =
          binary_relation_exprt(op, ID_lt, from_integer(0, distance_type));

      // shifting a non-zero value by more than its width is undefined;
      // yet this isn't an overflow
      const exprt dist_too_large = binary_predicate_exprt(
        distance, ID_gt, from_integer(op_width, distance_type));

      const exprt op_zero = equal_exprt(op, from_integer(0, op_type));

      auto new_type = to_bitvector_type(op_type);
      new_type.set_width(op_width * 2);

      const exprt op_ext = typecast_exprt(op, new_type);

      const exprt op_ext_shifted = shl_exprt(op_ext, distance);

      // get top bits of the shifted operand
      const exprt top_bits = extractbits_exprt(
        op_ext_shifted,
        new_type.get_width() - 1,
        op_width - 1,
        unsignedbv_typet(op_width + 1));

      const exprt top_bits_zero =
        equal_exprt(top_bits, from_integer(0, top_bits.type()));

      // a negative distance shift isn't an overflow;
      // a negative value shift isn't an overflow;
      // a shift that's too far isn't an overflow;
      // a shift of zero isn't overflow;
      // else check the top bits
      add_guarded_claim(
        disjunction({neg_value_shift,
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

  exprt overflow("overflow-"+expr.id_string(), bool_typet());
  overflow.operands()=expr.operands();

  if(expr.operands().size()>=3)
  {
    // The overflow checks are binary!
    // We break these up.

    for(std::size_t i=1; i<expr.operands().size(); i++)
    {
      exprt tmp;

      if(i==1)
        tmp=expr.op0();
      else
      {
        tmp=expr;
        tmp.operands().resize(i);
      }

      overflow.operands().resize(2);
      overflow.op0()=tmp;
      overflow.op1()=expr.operands()[i];

      std::string kind=
        type.id()==ID_unsignedbv?"unsigned":"signed";

      add_guarded_claim(
        not_exprt(overflow),
        "arithmetic overflow on "+kind+" "+expr.id_string(),
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }
  }
  else
  {
    std::string kind=
      type.id()==ID_unsignedbv?"unsigned":"signed";

    add_guarded_claim(
      not_exprt(overflow),
      "arithmetic overflow on "+kind+" "+expr.id_string(),
      "overflow",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_checkt::float_overflow_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_float_overflow_check)
    return;

  // First, check type.
  const typet &type=ns.follow(expr.type());

  if(type.id()!=ID_floatbv)
    return;

  // add overflow subgoal

  if(expr.id()==ID_typecast)
  {
    // Can overflow if casting from larger
    // to smaller type.
    assert(expr.operands().size()==1);

    if(ns.follow(expr.op0().type()).id()==ID_floatbv)
    {
      // float-to-float
      const isinf_exprt op0_inf(expr.op0());
      const isinf_exprt new_inf(expr);

      or_exprt overflow_check(op0_inf, not_exprt(new_inf));

      add_guarded_claim(
        overflow_check,
        "arithmetic overflow on floating-point typecast",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }
    else
    {
      // non-float-to-float
      const isinf_exprt new_inf(expr);

      add_guarded_claim(
        not_exprt(new_inf),
        "arithmetic overflow on floating-point typecast",
        "overflow",
        expr.find_source_location(),
        expr,
        guard);
    }

    return;
  }
  else if(expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);

    // Can overflow if dividing by something small
    const isinf_exprt new_inf(expr);
    const isinf_exprt op0_inf(expr.op0());

    or_exprt overflow_check(op0_inf, not_exprt(new_inf));

    add_guarded_claim(
      overflow_check,
      "arithmetic overflow on floating-point division",
      "overflow",
      expr.find_source_location(),
      expr,
      guard);

    return;
  }
  else if(expr.id()==ID_mod)
  {
    // Can't overflow
    return;
  }
  else if(expr.id()==ID_unary_minus)
  {
    // Can't overflow
    return;
  }
  else if(expr.id()==ID_plus || expr.id()==ID_mult ||
          expr.id()==ID_minus)
  {
    if(expr.operands().size()==2)
    {
      // Can overflow
      const isinf_exprt new_inf(expr);
      const isinf_exprt op0_inf(expr.op0());
      const isinf_exprt op1_inf(expr.op1());

      or_exprt overflow_check(op0_inf, op1_inf, not_exprt(new_inf));

      std::string kind=
        expr.id()==ID_plus?"addition":
        expr.id()==ID_minus?"subtraction":
        expr.id()==ID_mult?"multiplication":"";

      add_guarded_claim(
        overflow_check,
        "arithmetic overflow on floating-point "+kind,
        "overflow",
        expr.find_source_location(),
        expr,
        guard);

      return;
    }
    else if(expr.operands().size()>=3)
    {
      assert(expr.id()!=ID_minus);

      // break up
      exprt tmp=make_binary(expr);
      float_overflow_check(tmp, guard);
      return;
    }
  }
}

void goto_checkt::nan_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_nan_check)
    return;

  // first, check type
  if(expr.type().id()!=ID_floatbv)
    return;

  if(expr.id()!=ID_plus &&
     expr.id()!=ID_mult &&
     expr.id()!=ID_div &&
     expr.id()!=ID_minus)
    return;

  // add NaN subgoal

  exprt isnan;

  if(expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);

    // there a two ways to get a new NaN on division:
    // 0/0 = NaN and x/inf = NaN
    // (note that x/0 = +-inf for x!=0 and x!=inf)
    const and_exprt zero_div_zero(
      ieee_float_equal_exprt(expr.op0(), from_integer(0, expr.op0().type())),
      ieee_float_equal_exprt(expr.op1(), from_integer(0, expr.op1().type())));

    const isinf_exprt div_inf(expr.op1());

    isnan=or_exprt(zero_div_zero, div_inf);
  }
  else if(expr.id()==ID_mult)
  {
    if(expr.operands().size()>=3)
      return nan_check(make_binary(expr), guard);

    assert(expr.operands().size()==2);

    // Inf * 0 is NaN
    const and_exprt inf_times_zero(
      isinf_exprt(expr.op0()),
      ieee_float_equal_exprt(expr.op1(), from_integer(0, expr.op1().type())));

    const and_exprt zero_times_inf(
      ieee_float_equal_exprt(expr.op1(), from_integer(0, expr.op1().type())),
      isinf_exprt(expr.op0()));

    isnan=or_exprt(inf_times_zero, zero_times_inf);
  }
  else if(expr.id()==ID_plus)
  {
    if(expr.operands().size()>=3)
      return nan_check(make_binary(expr), guard);

    assert(expr.operands().size()==2);

    // -inf + +inf = NaN and +inf + -inf = NaN,
    // i.e., signs differ
    ieee_float_spect spec=ieee_float_spect(to_floatbv_type(expr.type()));
    exprt plus_inf=ieee_floatt::plus_infinity(spec).to_expr();
    exprt minus_inf=ieee_floatt::minus_infinity(spec).to_expr();

    isnan=
      or_exprt(
        and_exprt(
          equal_exprt(expr.op0(), minus_inf),
          equal_exprt(expr.op1(), plus_inf)),
        and_exprt(
          equal_exprt(expr.op0(), plus_inf),
          equal_exprt(expr.op1(), minus_inf)));
  }
  else if(expr.id()==ID_minus)
  {
    assert(expr.operands().size()==2);
    // +inf - +inf = NaN and -inf - -inf = NaN,
    // i.e., signs match

    ieee_float_spect spec=ieee_float_spect(to_floatbv_type(expr.type()));
    exprt plus_inf=ieee_floatt::plus_infinity(spec).to_expr();
    exprt minus_inf=ieee_floatt::minus_infinity(spec).to_expr();

    isnan=
      or_exprt(
        and_exprt(
          equal_exprt(expr.op0(), plus_inf),
          equal_exprt(expr.op1(), plus_inf)),
        and_exprt(
          equal_exprt(expr.op0(), minus_inf),
          equal_exprt(expr.op1(), minus_inf)));
  }
  else
    UNREACHABLE;

  add_guarded_claim(
    boolean_negate(isnan),
    "NaN on " + expr.id_string(),
    "NaN",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_checkt::pointer_rel_check(
  const exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_check)
    return;

  if(expr.operands().size()!=2)
    throw expr.id_string()+" takes two arguments";

  if(expr.op0().type().id()==ID_pointer &&
     expr.op1().type().id()==ID_pointer)
  {
    // add same-object subgoal

    if(enable_pointer_check)
    {
      exprt same_object=::same_object(expr.op0(), expr.op1());

      add_guarded_claim(
        same_object,
        "same object violation",
        "pointer",
        expr.find_source_location(),
        expr,
        guard);
    }
  }
}

void goto_checkt::pointer_overflow_check(
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

  exprt overflow("overflow-" + expr.id_string(), bool_typet());
  overflow.operands() = expr.operands();

  add_guarded_claim(
    not_exprt(overflow),
    "pointer arithmetic overflow on " + expr.id_string(),
    "overflow",
    expr.find_source_location(),
    expr,
    guard);
}

void goto_checkt::pointer_validity_check(
  const dereference_exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_check)
    return;

  const exprt &pointer=expr.pointer();

  auto conditions =
    address_check(pointer, size_of_expr(expr.type(), ns));

  for(const auto &c : conditions)
  {
    add_guarded_claim(
      c.assertion,
      "dereference failure: "+c.description,
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);
  }
}

goto_checkt::conditionst
goto_checkt::address_check(const exprt &address, const exprt &size)
{
  if(!enable_pointer_check)
    return {};

  PRECONDITION(address.type().id() == ID_pointer);
  const auto &pointer_type = to_pointer_type(address.type());

  local_bitvector_analysist::flagst flags =
    local_bitvector_analysis->get(current_target, address);

  // For Java, we only need to check for null
  if(mode == ID_java)
  {
    if(flags.is_unknown() || flags.is_null())
    {
      notequal_exprt not_eq_null(address, null_pointer_exprt(pointer_type));

      return {conditiont(not_eq_null, "reference is null")};
    }
    else
      return {};
  }
  else
  {
    conditionst conditions;
    exprt::operandst alloc_disjuncts;

    for(const auto &a : allocations)
    {
      typecast_exprt int_ptr(address, a.first.type());

      binary_relation_exprt lb_check(a.first, ID_le, int_ptr);

      plus_exprt ub(int_ptr, size, int_ptr.type());

      binary_relation_exprt ub_check(ub, ID_le, plus_exprt(a.first, a.second));

      alloc_disjuncts.push_back(and_exprt(lb_check, ub_check));
    }

    const exprt in_bounds_of_some_explicit_allocation =
      disjunction(alloc_disjuncts);

    if(flags.is_unknown() || flags.is_null())
    {
      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          not_exprt(null_pointer(address))),
        "pointer NULL"));
    }

    if(flags.is_unknown())
    {
      conditions.push_back(conditiont(
        not_exprt(invalid_pointer(address)),
        "pointer invalid"));
    }

    if(flags.is_uninitialized())
    {
      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          not_exprt(invalid_pointer(address))),
        "pointer uninitialized"));
    }

    if(flags.is_unknown() || flags.is_dynamic_heap())
    {
      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          not_exprt(deallocated(address, ns))),
        "deallocated dynamic object"));
    }

    if(flags.is_unknown() || flags.is_dynamic_local())
    {
      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          not_exprt(dead_object(address, ns))),
        "dead object"));
    }

    if(flags.is_unknown() || flags.is_dynamic_heap())
    {
      const or_exprt dynamic_bounds_violation(
        dynamic_object_lower_bound(address, ns, nil_exprt()),
        dynamic_object_upper_bound(address, ns, size));

      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          implies_exprt(
            malloc_object(address, ns), not_exprt(dynamic_bounds_violation))),
        "pointer outside dynamic object bounds"));
    }

    if(
      flags.is_unknown() || flags.is_dynamic_local() ||
      flags.is_static_lifetime())
    {
      const or_exprt object_bounds_violation(
        object_lower_bound(address, ns, nil_exprt()),
        object_upper_bound(address, ns, size));

      conditions.push_back(conditiont(
        or_exprt(
          in_bounds_of_some_explicit_allocation,
          implies_exprt(
            not_exprt(dynamic_object(address)),
            not_exprt(object_bounds_violation))),
        "pointer outside object bounds"));
    }

    if(flags.is_unknown() || flags.is_integer_address())
    {
      conditions.push_back(conditiont(
        implies_exprt(
          integer_address(address), in_bounds_of_some_explicit_allocation),
        "invalid integer address"));
    }

    return conditions;
  }
}

std::string goto_checkt::array_name(const exprt &expr)
{
  return ::array_name(ns, expr);
}

void goto_checkt::bounds_check(
  const index_exprt &expr,
  const guardt &guard)
{
  if(!enable_bounds_check)
    return;

  if(expr.find("bounds_check").is_not_nil() &&
     !expr.get_bool("bounds_check"))
    return;

  typet array_type=ns.follow(expr.array().type());

  if(array_type.id()==ID_pointer)
    throw "index got pointer as array type";
  else if(array_type.id()!=ID_array && array_type.id()!=ID_vector)
    throw "bounds check expected array or vector type, got "
      +array_type.id_string();

  std::string name=array_name(expr.array());

  const exprt &index=expr.index();
  object_descriptor_exprt ode;
  ode.build(expr, ns);

  if(index.type().id()!=ID_unsignedbv)
  {
    // we undo typecasts to signedbv
    if(index.id()==ID_typecast &&
       index.operands().size()==1 &&
       index.op0().type().id()==ID_unsignedbv)
    {
      // ok
    }
    else
    {
      const auto i = numeric_cast<mp_integer>(index);

      if(!i.has_value() || *i < 0)
      {
        exprt effective_offset=ode.offset();

        if(ode.root_object().id()==ID_dereference)
        {
          exprt p_offset=pointer_offset(
            to_dereference_expr(ode.root_object()).pointer());
          assert(p_offset.type()==effective_offset.type());

          effective_offset=plus_exprt(p_offset, effective_offset);
        }

        exprt zero=from_integer(0, ode.offset().type());
        assert(zero.is_not_nil());

        // the final offset must not be negative
        binary_relation_exprt inequality(effective_offset, ID_ge, zero);

        add_guarded_claim(
          inequality,
          name+" lower bound",
          "array bounds",
          expr.find_source_location(),
          expr,
          guard);
      }
    }
  }

  exprt type_matches_size=true_exprt();

  if(ode.root_object().id()==ID_dereference)
  {
    const exprt &pointer=
      to_dereference_expr(ode.root_object()).pointer();

    if_exprt size(
      dynamic_object(pointer),
      typecast_exprt(dynamic_size(ns), object_size(pointer).type()),
      object_size(pointer));

    plus_exprt effective_offset(ode.offset(), pointer_offset(pointer));

    assert(effective_offset.op0().type()==effective_offset.op1().type());
    if(effective_offset.type()!=size.type())
      size.make_typecast(effective_offset.type());

    binary_relation_exprt inequality(effective_offset, ID_lt, size);

    or_exprt precond(
      and_exprt(
        dynamic_object(pointer),
        not_exprt(malloc_object(pointer, ns))),
      inequality);

    add_guarded_claim(
      precond,
      name+" dynamic object upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);

    exprt type_size=size_of_expr(ode.root_object().type(), ns);
    if(type_size.is_not_nil())
      type_matches_size=
        equal_exprt(
          size,
          typecast_exprt(type_size, size.type()));
  }

  const exprt &size=array_type.id()==ID_array ?
                    to_array_type(array_type).size() :
                    to_vector_type(array_type).size();

  if(size.is_nil())
  {
    // Linking didn't complete, we don't have a size.
    // Not clear what to do.
  }
  else if(size.id()==ID_infinity)
  {
  }
  else if(size.is_zero() &&
          expr.array().id()==ID_member)
  {
    // a variable sized struct member
    //
    // Excerpt from the C standard on flexible array members:
    // However, when a . (or ->) operator has a left operand that is (a pointer
    // to) a structure with a flexible array member and the right operand names
    // that member, it behaves as if that member were replaced with the longest
    // array (with the same element type) that would not make the structure
    // larger than the object being accessed; [...]
    const exprt type_size = size_of_expr(ode.root_object().type(), ns);

    binary_relation_exprt inequality(
      typecast_exprt::conditional_cast(ode.offset(), type_size.type()),
      ID_lt,
      type_size);

    add_guarded_claim(
      implies_exprt(type_matches_size, inequality),
      name + " upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);
  }
  else
  {
    binary_relation_exprt inequality(index, ID_lt, size);

    // typecast size
    if(inequality.op1().type()!=inequality.op0().type())
      inequality.op1().make_typecast(inequality.op0().type());

    // typecast size
    if(inequality.op1().type()!=inequality.op0().type())
      inequality.op1().make_typecast(inequality.op0().type());

    add_guarded_claim(
      implies_exprt(type_matches_size, inequality),
      name+" upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_checkt::add_guarded_claim(
  const exprt &_expr,
  const std::string &comment,
  const std::string &property_class,
  const source_locationt &source_location,
  const exprt &src_expr,
  const guardt &guard)
{
  exprt expr(_expr);

  // first try simplifier on it
  if(enable_simplify)
    simplify(expr, ns);

  // throw away trivial properties?
  if(!retain_trivial && expr.is_true())
    return;

  // add the guard
  exprt guard_expr=guard.as_expr();

  exprt new_expr;

  if(guard_expr.is_true())
    new_expr.swap(expr);
  else
  {
    new_expr=exprt(ID_implies, bool_typet());
    new_expr.move_to_operands(guard_expr, expr);
  }

  if(assertions.insert(new_expr).second)
  {
    goto_program_instruction_typet type=
      enable_assert_to_assume?ASSUME:ASSERT;

    goto_programt::targett t=new_code.add_instruction(type);

    std::string source_expr_string;
    get_language_from_mode(mode)->from_expr(src_expr, source_expr_string, ns);

    t->guard.swap(new_expr);
    t->source_location=source_location;
    t->source_location.set_comment(comment+" in "+source_expr_string);
    t->source_location.set_property_class(property_class);
  }
}

void goto_checkt::check_rec(const exprt &expr, guardt &guard, bool address)
{
  // we don't look into quantifiers
  if(expr.id()==ID_exists || expr.id()==ID_forall)
    return;

  if(address)
  {
    if(expr.id()==ID_dereference)
    {
      assert(expr.operands().size()==1);
      check_rec(expr.op0(), guard, false);
    }
    else if(expr.id()==ID_index)
    {
      assert(expr.operands().size()==2);
      check_rec(expr.op0(), guard, true);
      check_rec(expr.op1(), guard, false);
    }
    else
    {
      forall_operands(it, expr)
        check_rec(*it, guard, true);
    }
    return;
  }

  if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    check_rec(expr.op0(), guard, true);
    return;
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(!expr.is_boolean())
      throw "`"+expr.id_string()+"' must be Boolean, but got "+
            expr.pretty();

    guardt old_guard=guard;

    for(const auto &op : expr.operands())
    {
      if(!op.is_boolean())
        throw "`"+expr.id_string()+"' takes Boolean operands only, but got "+
              op.pretty();

      check_rec(op, guard, false);

      if(expr.id()==ID_or)
        guard.add(not_exprt(op));
      else
        guard.add(op);
    }

    guard.swap(old_guard);

    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three arguments";

    if(!expr.op0().is_boolean())
    {
      std::string msg=
        "first argument of if must be boolean, but got "
        +expr.op0().pretty();
      throw msg;
    }

    check_rec(expr.op0(), guard, false);

    {
      guardt old_guard=guard;
      guard.add(expr.op0());
      check_rec(expr.op1(), guard, false);
      guard.swap(old_guard);
    }

    {
      guardt old_guard=guard;
      guard.add(not_exprt(expr.op0()));
      check_rec(expr.op2(), guard, false);
      guard.swap(old_guard);
    }

    return;
  }
  else if(expr.id()==ID_member &&
          to_member_expr(expr).struct_op().id()==ID_dereference)
  {
    const member_exprt &member=to_member_expr(expr);
    const dereference_exprt &deref=
      to_dereference_expr(member.struct_op());

    check_rec(deref.pointer(), guard, false);

    // avoid building the following expressions when pointer_validity_check
    // would return immediately anyway
    if(!enable_pointer_check)
      return;

    // we rewrite s->member into *(s+member_offset)
    // to avoid requiring memory safety of the entire struct

    exprt member_offset=member_offset_expr(member, ns);

    if(member_offset.is_not_nil())
    {
      pointer_typet new_pointer_type = to_pointer_type(deref.pointer().type());
      new_pointer_type.subtype() = expr.type();

      const exprt char_pointer =
        typecast_exprt::conditional_cast(
          deref.pointer(), pointer_type(char_type()));

      const exprt new_address = typecast_exprt(
        plus_exprt(
          char_pointer,
          typecast_exprt::conditional_cast(member_offset, pointer_diff_type())),
        char_pointer.type());

      const exprt new_address_casted =
        typecast_exprt::conditional_cast(new_address, new_pointer_type);

      dereference_exprt new_deref(new_address_casted, expr.type());
      new_deref.add_source_location() = deref.source_location();
      pointer_validity_check(new_deref, guard);

      return;
    }
  }

  forall_operands(it, expr)
    check_rec(*it, guard, false);

  if(expr.id()==ID_index)
  {
    bounds_check(to_index_expr(expr), guard);
  }
  else if(expr.id()==ID_div)
  {
    div_by_zero_check(to_div_expr(expr), guard);

    if(expr.type().id()==ID_signedbv)
      integer_overflow_check(expr, guard);
    else if(expr.type().id()==ID_floatbv)
    {
      nan_check(expr, guard);
      float_overflow_check(expr, guard);
    }
  }
  else if(expr.id()==ID_shl || expr.id()==ID_ashr || expr.id()==ID_lshr)
  {
    undefined_shift_check(to_shift_expr(expr), guard);

    if(expr.id()==ID_shl && expr.type().id()==ID_signedbv)
      integer_overflow_check(expr, guard);
  }
  else if(expr.id()==ID_mod)
  {
    mod_by_zero_check(to_mod_expr(expr), guard);
    mod_overflow_check(to_mod_expr(expr), guard);
  }
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult ||
          expr.id()==ID_unary_minus)
  {
    if(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv)
    {
      integer_overflow_check(expr, guard);
    }
    else if(expr.type().id()==ID_floatbv)
    {
      nan_check(expr, guard);
      float_overflow_check(expr, guard);
    }
    else if(expr.type().id()==ID_pointer)
    {
      pointer_overflow_check(expr, guard);
    }
  }
  else if(expr.id()==ID_typecast)
    conversion_check(expr, guard);
  else if(expr.id()==ID_le || expr.id()==ID_lt ||
          expr.id()==ID_ge || expr.id()==ID_gt)
    pointer_rel_check(expr, guard);
  else if(expr.id()==ID_dereference)
  {
    pointer_validity_check(to_dereference_expr(expr), guard);
  }
}

void goto_checkt::check(const exprt &expr)
{
  guardt guard;
  check_rec(expr, guard, false);
}

/// expand the r_ok and w_ok predicates
void goto_checkt::rw_ok_check(exprt &expr)
{
  for(auto &op : expr.operands())
    rw_ok_check(op);

  if(expr.id() == ID_r_ok || expr.id() == ID_w_ok)
  {
    // these get an address as first argument and a size as second
    DATA_INVARIANT(
      expr.operands().size() == 2, "r/w_ok must have two operands");

    const auto conditions = address_check(expr.op0(), expr.op1());
    exprt::operandst conjuncts;
    for(const auto &c : conditions)
      conjuncts.push_back(c.assertion);

    expr = conjunction(conjuncts);
  }
}

void goto_checkt::goto_check(
  goto_functiont &goto_function,
  const irep_idt &_mode)
{
  assertions.clear();
  mode = _mode;

  bool did_something = false;

  if(enable_pointer_check)
    local_bitvector_analysis =
      util_make_unique<local_bitvector_analysist>(goto_function);

  goto_programt &goto_program=goto_function.body;

  Forall_goto_program_instructions(it, goto_program)
  {
    current_target = it;
    goto_programt::instructiont &i=*it;

    new_code.clear();

    // we clear all recorded assertions if
    // 1) we want to generate all assertions or
    // 2) the instruction is a branch target
    if(retain_trivial ||
       i.is_target())
      assertions.clear();

    check(i.guard);

    // magic ERROR label?
    for(const auto &label : error_labels)
    {
      if(std::find(i.labels.begin(), i.labels.end(), label)!=i.labels.end())
      {
        goto_program_instruction_typet type=
          enable_assert_to_assume?ASSUME:ASSERT;

        goto_programt::targett t=new_code.add_instruction(type);

        t->guard=false_exprt();
        t->source_location=i.source_location;
        t->source_location.set_property_class("error label");
        t->source_location.set_comment("error label "+label);
        t->source_location.set("user-provided", true);
      }
    }

    if(i.is_other())
    {
      const irep_idt &statement=i.code.get(ID_statement);

      if(statement==ID_expression)
      {
        check(i.code);
      }
      else if(statement==ID_printf)
      {
        for(const auto &op : i.code.operands())
          check(op);
      }
    }
    else if(i.is_assign())
    {
      const code_assignt &code_assign=to_code_assign(i.code);

      check(code_assign.lhs());
      check(code_assign.rhs());

      // the LHS might invalidate any assertion
      invalidate(code_assign.lhs());
    }
    else if(i.is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(i.code);

      // for Java, need to check whether 'this' is null
      // on non-static method invocations
      if(mode==ID_java &&
         enable_pointer_check &&
         !code_function_call.arguments().empty() &&
         code_function_call.function().type().id()==ID_code &&
         to_code_type(code_function_call.function().type()).has_this())
      {
        exprt pointer=code_function_call.arguments()[0];

        local_bitvector_analysist::flagst flags =
          local_bitvector_analysis->get(current_target, pointer);

        if(flags.is_unknown() || flags.is_null())
        {
          notequal_exprt not_eq_null(
            pointer,
            null_pointer_exprt(to_pointer_type(pointer.type())));

          add_guarded_claim(
            not_eq_null,
            "this is null on method invocation",
            "pointer dereference",
            i.source_location,
            pointer,
            guardt());
        }
      }

      for(const auto &op : code_function_call.operands())
        check(op);

      // the call might invalidate any assertion
      assertions.clear();
    }
    else if(i.is_return())
    {
      if(i.code.operands().size()==1)
      {
        check(i.code.op0());
        // the return value invalidate any assertion
        invalidate(i.code.op0());
      }
    }
    else if(i.is_throw())
    {
      if(i.code.get_statement()==ID_expression &&
         i.code.operands().size()==1 &&
         i.code.op0().operands().size()==1)
      {
        // must not throw NULL

        exprt pointer=i.code.op0().op0();

        const notequal_exprt not_eq_null(
          pointer, null_pointer_exprt(to_pointer_type(pointer.type())));

        add_guarded_claim(
          not_eq_null,
          "throwing null",
          "pointer dereference",
          i.source_location,
          pointer,
          guardt());
      }

      // this has no successor
      assertions.clear();
    }
    else if(i.is_assert())
    {
      bool is_user_provided=i.source_location.get_bool("user-provided");

      rw_ok_check(i.guard);

      if((is_user_provided && !enable_assertions &&
          i.source_location.get_property_class()!="error label") ||
         (!is_user_provided && !enable_built_in_assertions))
      {
        i.make_skip();
        did_something = true;
      }
    }
    else if(i.is_assume())
    {
      if(!enable_assumptions)
      {
        i.make_skip();
        did_something = true;
      }
    }
    else if(i.is_dead())
    {
      if(enable_pointer_check)
      {
        assert(i.code.operands().size()==1);
        const symbol_exprt &variable=to_symbol_expr(i.code.op0());

        // is it dirty?
        if(local_bitvector_analysis->dirty(variable))
        {
          // need to mark the dead variable as dead
          goto_programt::targett t=new_code.add_instruction(ASSIGN);
          exprt address_of_expr=address_of_exprt(variable);
          exprt lhs=ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr();
          if(!base_type_eq(lhs.type(), address_of_expr.type(), ns))
            address_of_expr.make_typecast(lhs.type());
          const if_exprt rhs(
            side_effect_expr_nondett(bool_typet(), i.source_location),
            address_of_expr,
            lhs,
            lhs.type());
          t->source_location=i.source_location;
          t->code=code_assignt(lhs, rhs);
          t->code.add_source_location()=i.source_location;
        }
      }
    }
    else if(i.is_end_function())
    {
      if(i.function==goto_functionst::entry_point() &&
         enable_memory_leak_check)
      {
        const symbolt &leak=ns.lookup(CPROVER_PREFIX "memory_leak");
        const symbol_exprt leak_expr=leak.symbol_expr();

        // add self-assignment to get helpful counterexample output
        goto_programt::targett t=new_code.add_instruction();
        t->make_assignment();
        t->code=code_assignt(leak_expr, leak_expr);

        source_locationt source_location;
        source_location.set_function(i.function);

        equal_exprt eq(
          leak_expr,
          null_pointer_exprt(to_pointer_type(leak.type)));
        add_guarded_claim(
          eq,
          "dynamically allocated memory never freed",
          "memory-leak",
          source_location,
          eq,
          guardt());
      }
    }

    Forall_goto_program_instructions(i_it, new_code)
    {
      if(i_it->source_location.is_nil())
      {
        i_it->source_location.id(irep_idt());

        if(!it->source_location.get_file().empty())
          i_it->source_location.set_file(it->source_location.get_file());

        if(!it->source_location.get_line().empty())
          i_it->source_location.set_line(it->source_location.get_line());

        if(!it->source_location.get_function().empty())
          i_it->source_location.set_function(
            it->source_location.get_function());

        if(!it->source_location.get_column().empty())
          i_it->source_location.set_column(it->source_location.get_column());

        if(!it->source_location.get_java_bytecode_index().empty())
          i_it->source_location.set_java_bytecode_index(
            it->source_location.get_java_bytecode_index());
      }

      if(i_it->function.empty())
        i_it->function=it->function;
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

void goto_check(
  const namespacet &ns,
  const optionst &options,
  const irep_idt &mode,
  goto_functionst::goto_functiont &goto_function)
{
  goto_checkt goto_check(ns, options);
  goto_check.goto_check(goto_function, mode);
}

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions)
{
  goto_checkt goto_check(ns, options);

  goto_check.collect_allocations(goto_functions);

  Forall_goto_functions(it, goto_functions)
  {
    irep_idt mode=ns.lookup(it->first).mode;
    goto_check.goto_check(it->second, mode);
  }
}

void goto_check(
  const optionst &options,
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  goto_check(ns, options, goto_model.goto_functions);
}
