/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <location.h>
#include <i2string.h>
#include <expr_util.h>
#include <std_types.h>
#include <guard.h>
#include <simplify_expr.h>
#include <array_name.h>
#include <arith_tools.h>
#include <base_type.h>
#include <ieee_float.h>
#include <std_expr.h>
#include <find_symbols.h>

#include "goto_check.h"

class goto_checkt
{
public:
  goto_checkt(
    const namespacet &_ns,
    const optionst &_options):
    ns(_ns)
  {
    enable_bounds_check=_options.get_bool_option("bounds-check");
    enable_pointer_check=_options.get_bool_option("pointer-check");
    enable_div_by_zero_check=_options.get_bool_option("div-by-zero-check");
    enable_signed_overflow_check=_options.get_bool_option("signed-overflow-check");
    enable_unsigned_overflow_check=_options.get_bool_option("unsigned-overflow-check");
    enable_undefined_shift_check=_options.get_bool_option("undefined-shift-check");
    enable_float_overflow_check=_options.get_bool_option("float-overflow-check");
    enable_simplify=_options.get_bool_option("simplify");
    enable_nan_check=_options.get_bool_option("nan-check");
    generate_all_claims=_options.get_bool_option("all-claims");
    enable_assert_to_assume=_options.get_bool_option("assert-to-assume");
  }

  void goto_check(goto_programt &goto_program);
    
protected:
  const namespacet &ns;

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
    const std::string &property,
    const locationt &location,
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
  bool enable_div_by_zero_check;
  bool enable_signed_overflow_check;
  bool enable_unsigned_overflow_check;
  bool enable_undefined_shift_check;
  bool enable_float_overflow_check;
  bool enable_simplify;
  bool enable_nan_check;
  bool generate_all_claims;
  bool enable_assert_to_assume;
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
    expr.find_location(),
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
      expr.find_location(),
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
      expr.find_location(),
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
    expr.find_location(),
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
      if(old_type.id()==ID_signedbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);
        unsigned old_width=old_type.get_int(ID_width);
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
          expr.find_location(),
          guard);
      }
      else if(old_type.id()==ID_unsignedbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);
        unsigned old_width=old_type.get_int(ID_width);
        if(new_width>=old_width+1) return; // always ok

        binary_relation_exprt no_overflow_upper(ID_le);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=from_integer(power(2, new_width-1)-1, old_type);

        add_guarded_claim(
          no_overflow_upper,
          "arithmetic overflow on unsigned to signed type conversion",
          "overflow",
          expr.find_location(),
          guard);
      }
      else if(old_type.id()==ID_floatbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);

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
          expr.find_location(),
          guard);
      }
    }
    else if(type.id()==ID_unsignedbv)
    {
      // todo
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
        expr.find_location(),
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
        expr.find_location(),
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
    
      add_guarded_claim(
        not_exprt(overflow),
        "arithmetic overflow on "+expr.id_string(),
        "overflow",
        expr.find_location(),
        guard);
    }
  }
  else
  {
    add_guarded_claim(
      not_exprt(overflow),
      "arithmetic overflow on "+expr.id_string(),
      "overflow",
      expr.find_location(),
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
  
  if(type.id()==ID_floatbv)
    return;

  #if 0
  // add overflow subgoal

  if(expr.id()==ID_typecast)
  {
    // conversion to signed int may overflow
  
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    const typet &old_type=ns.follow(expr.op0().type());
    
    if(type.id()==ID_signedbv)
    {
      if(old_type.id()==ID_signedbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);
        unsigned old_width=old_type.get_int(ID_width);
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
          expr.find_location(),
          guard);
      }
      else if(old_type.id()==ID_unsignedbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);
        unsigned old_width=old_type.get_int(ID_width);
        if(new_width>=old_width+1) return; // always ok

        binary_relation_exprt no_overflow_upper(ID_le);
        no_overflow_upper.lhs()=expr.op0();
        no_overflow_upper.rhs()=from_integer(power(2, new_width-1)-1, old_type);

        add_guarded_claim(
          no_overflow_upper,
          "arithmetic overflow on unsigned to signed type conversion",
          "overflow",
          expr.find_location(),
          guard);
      }
      else if(old_type.id()==ID_floatbv)
      {
        unsigned new_width=expr.type().get_int(ID_width);

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
          expr.find_location(),
          guard);
      }
    }
    else if(type.id()==ID_unsignedbv)
    {
      // todo
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
        expr.find_location(),
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
        expr.find_location(),
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
    
      add_guarded_claim(
        not_exprt(overflow),
        "arithmetic overflow on "+expr.id_string(),
        "overflow",
        expr.find_location(),
        guard);
    }
  }
  else
  {
    add_guarded_claim(
      not_exprt(overflow),
      "arithmetic overflow on "+expr.id_string(),
      "overflow",
      expr.find_location(),
      guard);
  }
  #endif
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

  // add nan subgoal

  exprt isnan(ID_isnan, bool_typet());
  isnan.copy_to_operands(expr);

  isnan.make_not();

  add_guarded_claim(
    isnan,
    "NaN on "+expr.id_string(),
    "NaN",
    expr.find_location(),
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
      exprt same_object("same-object", bool_typet());
      same_object.copy_to_operands(expr.op0(), expr.op1());

      add_guarded_claim(
        same_object,
        "same object violation",
        "pointer",
        expr.find_location(),
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
  #if 0
  if(!enable_pointer_check)
    return;

  const exprt &pointer_expr=expr.op0();
  const typet &pointer_expr_type=ns.follow(pointer_expr.type());

  assert(pointer_expr_type.id()==ID_pointer);

  const pointer_typet &pointer_type=to_pointer_type(pointer_expr_type);

  // NULL?
  {
    null_pointer_exprt null_pointer(pointer_type);

    predicate_exprt same_object(ID_same_object);
    same_object.copy_to_operands(pointer_expr, null_pointer);

    add_guarded_claim(
      same_object,
      "NULL pointer",
      "pointer dereference",
      expr.find_location(),
      guard);
  }
  
  // Invalid?
  {
    predicate_exprt invalid_pointer("invalid-pointer");
    invalid_pointer.copy_to_operands(pointer_expr);

    add_guarded_claim(
      invalid_pointer,
      "invalid pointer",
      "pointer dereference",
      expr.find_location(),
      guard);
  }
  
  exprt offset=unary_exprt(
    ID_pointer_offset, pointer_expr,
    pointer_type.difference_type());

  // lower bound is easy
  {
    binary_relation_exprt
      offset_lower_bound(offset, ID_lt,
                         gen_zero(offset.type()));

    add_guarded_claim(
      offset_lower_bound,
      "object lower bound",
      "pointer dereference",
      expr.find_location(),
      guard);
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
  {
    std::cerr << expr.pretty() << std::endl;
    throw "index got incomplete array";
  }
  else if(array_type.id()!=ID_array)
    throw "bounds check expected array type, got "+array_type.id_string();

  std::string name=array_name(expr.array());
  
  const exprt &index=expr.index();

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
        exprt zero=gen_zero(index.type());

        if(zero.is_nil())
          throw "no zero constant of index type "+
            index.type().to_string();

        exprt inequality(ID_ge, bool_typet());
        inequality.copy_to_operands(index, zero);

        add_guarded_claim(
          inequality,
          name+" lower bound",
          "array bounds",
          expr.find_location(),
          guard);
      }
    }
  }

  {
    if(to_array_type(array_type).size().is_nil())
      throw "index array operand of wrong type";

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
        expr.find_location(),
        guard);
    }
  }
}

/*******************************************************************\

Function: goto_checkt::array_size_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void goto_checkt::array_size_check(
  const exprt &expr,
  const irept &location)
{
  if(expr.type().id()==ID_array)
  {
    const exprt &size=(exprt &)expr.type().find(ID_size);

    if(size.type().id()==ID_unsignedbv)
    {
      // nothing to do
    }
    else
    {
      exprt zero=gen_zero(size.type());

      if(zero.is_nil())
        throw "no zero constant of index type "+
          size.type().to_string();

      exprt inequality(ID_ge, bool_typet());
      inequality.copy_to_operands(size, zero);

      std::string name=array_name(expr);

      guardt guard;
      add_guarded_claim(inequality, name+" size", location, guard);
    }
  }
}
#endif

/*******************************************************************\

Function: goto_checkt::add_guarded_claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_checkt::add_guarded_claim(
  const exprt &_expr,
  const std::string &comment,
  const std::string &property,
  const locationt &location,
  const guardt &guard)
{
  exprt expr(_expr);

  // first try simplifier on it
  if(enable_simplify)
    simplify(expr, ns);

  if(!generate_all_claims && expr.is_true())
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

    t->guard.swap(new_expr);
    t->location=location;
    t->location.set_comment(comment);
    t->location.set_property(property);
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
        guard.add(gen_not(op));
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
      guard.add(gen_not(expr.op0()));
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
      integer_overflow_check(expr, guard);
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

 Purpose:

\*******************************************************************/

void goto_checkt::goto_check(goto_programt &goto_program)
{
  assertions.clear();

  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    goto_programt::instructiont &i=*it;
    
    new_code.clear();

    // we clear all recorded assertions if
    // 1) we want to generate all assertions or
    // 2) the instruction is a branch target
    if(generate_all_claims ||
       i.is_target())
      assertions.clear();
    
    check(i.guard);

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
    
    for(goto_programt::instructionst::iterator
        i_it=new_code.instructions.begin();
        i_it!=new_code.instructions.end();
        i_it++)
    {
      if(i_it->location.is_nil()) i_it->location=it->location;
      if(i_it->function==irep_idt()) i_it->function=it->function;
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
  goto_programt &goto_program)
{
  goto_checkt goto_check(ns, options);
  goto_check.goto_check(goto_program);
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
    goto_check.goto_check(it->second.body);
  }
}                    
