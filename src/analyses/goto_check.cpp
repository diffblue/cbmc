/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/simplify_expr.h>
#include <util/array_name.h>
#include <util/ieee_float.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/guard.h>
#include <util/base_type.h>
#include <util/pointer_predicates.h>
#include <util/cprover_prefix.h>

#include "local_bitvector_analysis.h"
#include "goto_check.h"

class goto_checkt
{
public:
  goto_checkt(
    const namespacet &_ns,
    const optionst &_options):
    ns(_ns),
    local_bitvector_analysis(0)
  {
    enable_bounds_check=_options.get_bool_option("bounds-check");
    enable_pointer_check=_options.get_bool_option("pointer-check");
    enable_memory_leak_check=_options.get_bool_option("memory-leak-check");
    enable_div_by_zero_check=_options.get_bool_option("div-by-zero-check");
    enable_signed_overflow_check=_options.get_bool_option("signed-overflow-check");
    enable_unsigned_overflow_check=_options.get_bool_option("unsigned-overflow-check");
    enable_undefined_shift_check=_options.get_bool_option("undefined-shift-check");
    enable_float_overflow_check=_options.get_bool_option("float-overflow-check");
    enable_simplify=_options.get_bool_option("simplify");
    enable_nan_check=_options.get_bool_option("nan-check");
    retain_trivial=_options.get_bool_option("retain-trivial");
    enable_assert_to_assume=_options.get_bool_option("assert-to-assume");
    enable_assertions=_options.get_bool_option("assertions");
    enable_assumptions=_options.get_bool_option("assumptions");    
    error_labels=_options.get_list_option("error-label");
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  void goto_check(goto_functiont &goto_function);
    
protected:
  const namespacet &ns;
  local_bitvector_analysist *local_bitvector_analysis;
  goto_programt::const_targett t;

  void check_rec(const exprt &expr, guardt &guard, bool address);
  void check(const exprt &expr);

  void bounds_check(const index_exprt &expr, const guardt &guard);
  void div_by_zero_check(const div_exprt &expr, const guardt &guard);
  void mod_by_zero_check(const mod_exprt &expr, const guardt &guard);
  void undefined_shift_check(const shift_exprt &expr, const guardt &guard);
  void pointer_rel_check(const exprt &expr, const guardt &guard);
  void pointer_validity_check(const dereference_exprt &expr, const guardt &guard);
  void integer_overflow_check(const exprt &expr, const guardt &guard);
  void float_overflow_check(const exprt &expr, const guardt &guard);
  void nan_check(const exprt &expr, const guardt &guard);

  std::string array_name(const exprt &expr);

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
  
  static bool has_dereference(const exprt &src)
  {
    if(src.id()==ID_dereference)
      return true;
    else
    {
      forall_operands(it, src)
        if(has_dereference(*it)) return true;

      return false;
    }
  }

  bool enable_bounds_check;
  bool enable_pointer_check;  
  bool enable_memory_leak_check;
  bool enable_div_by_zero_check;
  bool enable_signed_overflow_check;
  bool enable_unsigned_overflow_check;
  bool enable_undefined_shift_check;
  bool enable_float_overflow_check;
  bool enable_simplify;
  bool enable_nan_check;
  bool retain_trivial;
  bool enable_assert_to_assume;
  bool enable_assertions;
  bool enable_assumptions;

  typedef optionst::value_listt error_labelst;
  error_labelst error_labels;
};

/*******************************************************************\

Function: goto_checkt::invalidate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      
      if(has_symbol(*it, find_symbols_set) ||
         has_dereference(*it))
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

/*******************************************************************\

Function: goto_checkt::div_by_zero_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::div_by_zero_check(
  const div_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero=gen_zero(expr.op1().type());

  if(zero.is_nil())
    throw "no zero of argument type of operator "+expr.id_string();

  exprt inequality(ID_notequal, bool_typet());
  inequality.copy_to_operands(expr.op1(), zero);

  add_guarded_claim(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

/*******************************************************************\

Function: goto_checkt::undefined_shift_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      expr.distance(), ID_ge, gen_zero(distance_type));

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
      
    binary_relation_exprt inequality(
      expr.distance(), ID_lt, width_expr);

    add_guarded_claim(
      inequality,
      "shift distance too large",
      "undefined-shift",
      expr.find_source_location(),
      expr,
      guard);
  }
}

/*******************************************************************\

Function: goto_checkt::mod_by_zero_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::mod_by_zero_check(
  const mod_exprt &expr,
  const guardt &guard)
{
  if(!enable_div_by_zero_check)
    return;

  // add divison by zero subgoal

  exprt zero=gen_zero(expr.op1().type());

  if(zero.is_nil())
    throw "no zero of argument type of operator "+expr.id_string();

  exprt inequality(ID_notequal, bool_typet());
  inequality.copy_to_operands(expr.op1(), zero);

  add_guarded_claim(
    inequality,
    "division by zero",
    "division-by-zero",
    expr.find_source_location(),
    expr,
    guard);
}

/*******************************************************************\

Function: goto_checkt::integer_overflow_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

  if(expr.id()==ID_typecast)
  {
    // conversion to signed int may overflow
  
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    const typet &old_type=ns.follow(expr.op0().type());
    
    if(type.id()==ID_signedbv)
    {
      unsigned new_width=to_signedbv_type(type).get_width();

      if(old_type.id()==ID_signedbv) // signed -> signed
      {
        unsigned old_width=to_signedbv_type(old_type).get_width();
        if(new_width>=old_width) return; // always ok

        binary_relation_exprt no_overflow_upper(ID_le);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=from_integer(power(2, new_width-1)-1, old_type);

        binary_relation_exprt no_overflow_lower(ID_ge);
        no_overflow_lower.lhs()=expr.op0();
        no_overflow_lower.rhs()=from_integer(-power(2, new_width-1), old_type);

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
        unsigned old_width=to_unsignedbv_type(old_type).get_width();
        if(new_width>=old_width+1) return; // always ok

        binary_relation_exprt no_overflow_upper(ID_le);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=from_integer(power(2, new_width-1)-1, old_type);

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
        binary_relation_exprt no_overflow_upper(ID_lt);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=upper.to_expr();

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-power(2, new_width-1)-1);
        binary_relation_exprt no_overflow_lower(ID_gt);
        no_overflow_lower.lhs()=expr.op0();
        no_overflow_lower.rhs()=lower.to_expr();

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
      unsigned new_width=to_unsignedbv_type(type).get_width();

      if(old_type.id()==ID_signedbv) // signed -> unsigned
      {
        unsigned old_width=to_signedbv_type(old_type).get_width();

        if(new_width>=old_width-1)
        {
          // only need lower bound check
          binary_relation_exprt no_overflow_lower(ID_ge);
          no_overflow_lower.lhs()=expr.op0();
          no_overflow_lower.rhs()=from_integer(0, old_type);

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
          binary_relation_exprt no_overflow_upper(ID_le);
          no_overflow_upper.lhs()=expr.op0();
          no_overflow_upper.rhs()=from_integer(power(2, new_width)-1, old_type);

          binary_relation_exprt no_overflow_lower(ID_ge);
          no_overflow_lower.lhs()=expr.op0();
          no_overflow_lower.rhs()=from_integer(0, old_type);

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
        unsigned old_width=to_unsignedbv_type(old_type).get_width();
        if(new_width>=old_width) return; // always ok

        binary_relation_exprt no_overflow_upper(ID_le);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=from_integer(power(2, new_width)-1, old_type);

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
        binary_relation_exprt no_overflow_upper(ID_lt);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=upper.to_expr();

        ieee_floatt lower(to_floatbv_type(old_type));
        lower.from_integer(-1);
        binary_relation_exprt no_overflow_lower(ID_gt);
        no_overflow_lower.lhs()=expr.op0();
        no_overflow_lower.rhs()=lower.to_expr();

        add_guarded_claim(
          and_exprt(no_overflow_lower, no_overflow_upper),
          "arithmetic overflow on float to unsigned integer type conversion",
          "overflow",
          expr.find_source_location(),
          expr,
          guard);
      }
    }

    return;
  }
  else if(expr.id()==ID_div)
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
  else if(expr.id()==ID_mod)
  {
    // these can't overflow
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

  exprt overflow("overflow-"+expr.id_string(), bool_typet());
  overflow.operands()=expr.operands();

  if(expr.operands().size()>=3)
  {
    // The overflow checks are binary!
    // We break these up.
  
    for(unsigned i=1; i<expr.operands().size(); i++)
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
      expr.find_location(),
      expr,
      guard);
  }
}

/*******************************************************************\

Function: goto_checkt::float_overflow_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      unary_exprt op0_inf(ID_isinf, expr.op0(), bool_typet());
      unary_exprt new_inf(ID_isinf, expr, bool_typet());
    
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
      unary_exprt new_inf(ID_isinf, expr, bool_typet());
    
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
    unary_exprt new_inf(ID_isinf, expr, bool_typet());
    unary_exprt op0_inf(ID_isinf, expr.op0(), bool_typet());
    
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
      unary_exprt new_inf(ID_isinf, expr, bool_typet());      
      unary_exprt op0_inf(ID_isinf, expr.op0(), bool_typet());
      unary_exprt op1_inf(ID_isinf, expr.op1(), bool_typet());
      
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

/*******************************************************************\

Function: goto_checkt::nan_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    exprt zero_div_zero=and_exprt(
      ieee_float_equal_exprt(expr.op0(), gen_zero(expr.op0().type())),
      ieee_float_equal_exprt(expr.op1(), gen_zero(expr.op1().type())));

    exprt div_inf=unary_exprt(ID_isinf, expr.op1(), bool_typet());
    
    isnan=or_exprt(zero_div_zero, div_inf);
  }
  else if(expr.id()==ID_mult)
  {
    if(expr.operands().size()>=3)
      return nan_check(make_binary(expr), guard);

    assert(expr.operands().size()==2);

    // Inf * 0 is NaN
    exprt inf_times_zero=and_exprt(
      unary_exprt(ID_isinf, expr.op0(), bool_typet()),
      ieee_float_equal_exprt(expr.op1(), gen_zero(expr.op1().type())));

    exprt zero_times_inf=and_exprt(
      ieee_float_equal_exprt(expr.op1(), gen_zero(expr.op1().type())),
      unary_exprt(ID_isinf, expr.op0(), bool_typet()));

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

    isnan=or_exprt(
      and_exprt(equal_exprt(expr.op0(), minus_inf), equal_exprt(expr.op1(), plus_inf)),
      and_exprt(equal_exprt(expr.op0(), plus_inf), equal_exprt(expr.op1(), minus_inf)));
  }
  else if(expr.id()==ID_minus)
  {
    assert(expr.operands().size()==2);
    // +inf - +inf = NaN and -inf - -inf = NaN,
    // i.e., signs match

    ieee_float_spect spec=ieee_float_spect(to_floatbv_type(expr.type()));
    exprt plus_inf=ieee_floatt::plus_infinity(spec).to_expr();
    exprt minus_inf=ieee_floatt::minus_infinity(spec).to_expr();

    isnan=or_exprt(
      and_exprt(equal_exprt(expr.op0(), plus_inf), equal_exprt(expr.op1(), plus_inf)),
      and_exprt(equal_exprt(expr.op0(), minus_inf), equal_exprt(expr.op1(), minus_inf)));
  }
  else
    assert(false);

  isnan.make_not();

  add_guarded_claim(
    isnan,
    "NaN on "+expr.id_string(),
    "NaN",
    expr.find_source_location(),
    expr,
    guard);
}

/*******************************************************************\

Function: goto_checkt::pointer_rel_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::pointer_rel_check(
  const exprt &expr,
  const guardt &guard)
{
  if(expr.operands().size()!=2)
    throw expr.id_string()+" takes one argument";

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

/*******************************************************************\

Function: goto_checkt::pointer_validity_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::pointer_validity_check(
  const dereference_exprt &expr,
  const guardt &guard)
{
  if(!enable_pointer_check)
    return;

  const exprt &pointer=expr.op0();
  const typet &pointer_type=to_pointer_type(ns.follow(pointer.type()));

  assert(base_type_eq(pointer_type.subtype(), expr.type(), ns));

  #if 0
  add_guarded_claim(
    good_pointer(expr.pointer()),
    "dereference failure: pointer not valid",
    "pointer dereference",
    expr.find_source_location(),
    expr,
    guard);    
  #else
  
  local_bitvector_analysist::flagst flags=
    local_bitvector_analysis->get(t, pointer);
    
  const typet &dereference_type=pointer_type.subtype();

  if(flags.is_unknown() || flags.is_null())
  {
    add_guarded_claim(
      not_exprt(null_pointer(pointer)),
      "dereference failure: pointer NULL",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);
  }

  if(flags.is_unknown())
    add_guarded_claim(
      not_exprt(invalid_pointer(pointer)),
      "dereference failure: pointer invalid",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);

  if(flags.is_uninitialized())
    add_guarded_claim(
      not_exprt(invalid_pointer(pointer)),
      "dereference failure: pointer uninitialized",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);

  if(flags.is_unknown() || flags.is_dynamic_heap())
    add_guarded_claim(
      not_exprt(deallocated(pointer, ns)),
      "dereference failure: deallocated dynamic object",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);

  if(flags.is_unknown() || flags.is_dynamic_local())
    add_guarded_claim(
      not_exprt(dead_object(pointer, ns)),
      "dereference failure: dead object",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);

  if(enable_bounds_check)
  {
    if(flags.is_unknown() || flags.is_dynamic_heap())
    {
      exprt dynamic_bounds=
        or_exprt(dynamic_object_lower_bound(pointer),
                 dynamic_object_upper_bound(pointer, dereference_type, ns));

      add_guarded_claim(
        implies_exprt(malloc_object(pointer, ns), not_exprt(dynamic_bounds)),
        "dereference failure: dynamic object bounds",
        "pointer dereference",
        expr.find_source_location(),
        expr,
        guard);
    }
  }

  if(enable_bounds_check)
  {
    if(flags.is_unknown() ||
       flags.is_dynamic_local() ||
       flags.is_static_lifetime())
    {
      exprt object_bounds=
        or_exprt(object_lower_bound(pointer),
                 object_upper_bound(pointer, dereference_type, ns));

      add_guarded_claim(
        or_exprt(dynamic_object(pointer), not_exprt(object_bounds)),
        "dereference failure: object bounds",
        "pointer dereference",
        expr.find_source_location(),
        expr,
        guard);
    }
  }

  #endif
}

/*******************************************************************\

Function: goto_checkt::array_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string goto_checkt::array_name(const exprt &expr)
{
  return ::array_name(ns, expr);
}

/*******************************************************************\

Function: goto_checkt::bounds_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    return; // done by the pointer code
  else if(array_type.id()==ID_incomplete_array)
    throw "index got incomplete array";
  else if(array_type.id()!=ID_array)
    throw "bounds check expected array type, got "+array_type.id_string();

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
      mp_integer i;
      
      if(!to_integer(index, i) && i>=0)
      {
        // ok
      }
      else
      {
        exprt effective_offset=ode.offset();

        if(ode.root_object().id()==ID_dereference)
        {
          exprt p_offset=pointer_offset(
            to_dereference_expr(ode.root_object()).pointer());
          assert(p_offset.type()==effective_offset.type());

          effective_offset=plus_exprt(p_offset, effective_offset);
        }

        exprt zero=gen_zero(ode.offset().type());
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
    assert(effective_offset.type()==size.type());

    binary_relation_exprt inequality(effective_offset, ID_lt, size);

    or_exprt precond(
      and_exprt(
        dynamic_object(pointer),
        not_exprt(malloc_object(pointer, ns))),
      inequality);

    add_guarded_claim(
      precond,
      name+" upper bound",
      "array bounds",
      expr.find_source_location(),
      expr,
      guard);
  }
  else if(to_array_type(array_type).size().is_nil())
  {
    // Linking didn't complete, we don't have a size.
    // Not clear what to do.
  }
  else
  {
    const exprt &size=to_array_type(array_type).size();

    if(size.id()==ID_infinity)
    {
    }
    else if(size.is_zero() &&
            expr.array().id()==ID_member)
    {
      // a variable sized struct member
    }
    else
    {
      binary_relation_exprt inequality(index, ID_lt, size);

      // typecast size
      if(inequality.op1().type()!=inequality.op0().type())
        inequality.op1().make_typecast(inequality.op0().type());

      add_guarded_claim(
        inequality,
        name+" upper bound",
        "array bounds",
        expr.find_source_location(),
        expr,
        guard);
    }
  }
}

/*******************************************************************\

Function: goto_checkt::add_guarded_claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    
    std::string source_expr_string=from_expr(ns, "", src_expr);

    t->guard.swap(new_expr);
    t->source_location=source_location;
    t->source_location.set_comment(comment+" in "+source_expr_string);
    t->source_location.set_property_class(property_class);
  }
}

/*******************************************************************\

Function: goto_checkt::check_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::check_rec(
  const exprt &expr,
  guardt &guard,
  bool address)
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

    unsigned old_guards=guard.size();

    for(unsigned i=0; i<expr.operands().size(); i++)
    {
      const exprt &op=expr.operands()[i];

      if(!op.is_boolean())
        throw "`"+expr.id_string()+"' takes Boolean operands only, but got "+
              op.pretty();

      check_rec(op, guard, false);

      if(expr.id()==ID_or)
        guard.add(not_exprt(op));
      else
        guard.add(op);
    }

    guard.resize(old_guards);

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
        +expr.op0().to_string();
      throw msg;
    }

    check_rec(expr.op0(), guard, false);

    {
      unsigned old_guard=guard.size();
      guard.add(expr.op0());
      check_rec(expr.op1(), guard, false);
      guard.resize(old_guard);
    }

    {
      unsigned old_guard=guard.size();
      guard.add(not_exprt(expr.op0()));
      check_rec(expr.op2(), guard, false);
      guard.resize(old_guard);
    }

    return;
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
  }
  else if(expr.id()==ID_mod)
  {
    mod_by_zero_check(to_mod_expr(expr), guard);
  }
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult ||
          expr.id()==ID_unary_minus ||
          expr.id()==ID_typecast)
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
  }
  else if(expr.id()==ID_le || expr.id()==ID_lt ||
          expr.id()==ID_ge || expr.id()==ID_gt)
    pointer_rel_check(expr, guard);
  else if(expr.id()==ID_dereference)
    pointer_validity_check(to_dereference_expr(expr), guard);
}

/*******************************************************************\

Function: goto_checkt::check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::check(const exprt &expr)
{
  guardt guard;
  check_rec(expr, guard, false);
}

/*******************************************************************\

Function: goto_checkt::goto_check

  Inputs:

 Outputs:

 Purpose:[B

\*******************************************************************/

void goto_checkt::goto_check(goto_functiont &goto_function)
{
  assertions.clear();
  
  local_bitvector_analysist local_bitvector_analysis_obj(goto_function);
  local_bitvector_analysis=&local_bitvector_analysis_obj;

  goto_programt &goto_program=goto_function.body;

  Forall_goto_program_instructions(it, goto_program)
  {
    t=it;
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
    for(optionst::value_listt::const_iterator
        l_it=error_labels.begin();
        l_it!=error_labels.end();
        l_it++)
    {
      if(std::find(i.labels.begin(), i.labels.end(), *l_it)!=i.labels.end())
      {
        goto_program_instruction_typet type=
          enable_assert_to_assume?ASSUME:ASSERT;

        goto_programt::targett t=new_code.add_instruction(type);

        t->guard=false_exprt();
        t->source_location=i.source_location;
        t->source_location.set_property_class("error label");
        t->source_location.set_comment("error label "+*l_it);
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
        forall_operands(it, i.code)
          check(*it);
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
    
      forall_operands(it, code_function_call)
        check(*it);

      // the call might invalidate any assertion
      assertions.clear();
    }
    else if(i.is_return())
    {
      if(i.code.operands().size()==1)
        check(i.code.op0());
        
      // this has no successor
      assertions.clear();
    }
    else if(i.is_throw())
    {
      // this has no successor
      assertions.clear();
    }
    else if(i.is_assert())
    {
      if(i.source_location.get_bool("user-provided") &&
         i.source_location.get_property_class()!="error label" &&
         !enable_assertions)
        i.type=SKIP;
    }
    else if(i.is_assume())
    {
      if(!enable_assumptions)
        i.type=SKIP;
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
          exprt rhs=if_exprt(
            side_effect_expr_nondett(bool_typet()), address_of_expr, lhs, lhs.type());
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

        equal_exprt eq(leak_expr, gen_zero(ns.follow(leak.type)));
        add_guarded_claim(
          eq,
          "dynamically allocated memory never freed",
          "memory-leak",
          source_location,
          eq,
          guardt());
      }
    }

    for(goto_programt::instructionst::iterator
        i_it=new_code.instructions.begin();
        i_it!=new_code.instructions.end();
        i_it++)
    {
      if(i_it->source_location.is_nil())
      {
        i_it->source_location.id(irep_idt());

        if(it->source_location.get_file()!=irep_idt())
          i_it->source_location.set_file(it->source_location.get_file());

        if(it->source_location.get_line()!=irep_idt())
          i_it->source_location.set_line(it->source_location.get_line());

        if(it->source_location.get_function()!=irep_idt())
          i_it->source_location.set_function(it->source_location.get_function());

        if(it->source_location.get_column()!=irep_idt())
          i_it->source_location.set_column(it->source_location.get_column());
      }
      
      if(i_it->function==irep_idt()) i_it->function=it->function;
    }
      
    // insert new instructions -- make sure targets are not moved

    while(!new_code.instructions.empty())
    {
      goto_program.insert_before_swap(it, new_code.instructions.front());
      new_code.instructions.pop_front();
      it++;
    }
  }
}

/*******************************************************************\

Function: goto_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst::goto_functiont &goto_function)
{
  goto_checkt goto_check(ns, options);
  goto_check.goto_check(goto_function);
}                    

/*******************************************************************\

Function: goto_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions)
{
  goto_checkt goto_check(ns, options);
  
  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    goto_check.goto_check(it->second);
  }
}                    

/*******************************************************************\

Function: goto_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_check(
  const optionst &options,
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  goto_checkt goto_check(ns, options);
  
  for(goto_functionst::function_mapt::iterator
      it=goto_model.goto_functions.function_map.begin();
      it!=goto_model.goto_functions.function_map.end();
      it++)
  {
    goto_check.goto_check(it->second);
  }
}                    
