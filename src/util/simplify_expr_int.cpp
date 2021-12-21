/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "c_types.h"
#include "config.h"
#include "expr_util.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "invariant.h"
#include "mathematical_types.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "pointer_offset_size.h"
#include "rational.h"
#include "rational_tools.h"
#include "simplify_utils.h"
#include "std_expr.h"

simplify_exprt::resultt<>
simplify_exprt::simplify_bswap(const bswap_exprt &expr)
{
  if(expr.type().id() == ID_unsignedbv && expr.op().is_constant())
  {
    auto bits_per_byte = expr.get_bits_per_byte();
    std::size_t width=to_bitvector_type(expr.type()).get_width();
    const mp_integer value =
      numeric_cast_v<mp_integer>(to_constant_expr(expr.op()));
    std::vector<mp_integer> bytes;

    // take apart
    for(std::size_t bit = 0; bit < width; bit += bits_per_byte)
      bytes.push_back((value >> bit)%power(2, bits_per_byte));

    // put back together, but backwards
    mp_integer new_value=0;
    for(std::size_t bit = 0; bit < width; bit += bits_per_byte)
    {
      INVARIANT(
        !bytes.empty(),
        "bytes is not empty because we just pushed just as many elements on "
        "top of it as we are popping now");
      new_value+=bytes.back()<<bit;
      bytes.pop_back();
    }

    return from_integer(new_value, expr.type());
  }

  return unchanged(expr);
}

//! produce a sum of two constant expressions of the same type
//! \return 'false' iff this was successful
static bool sum_expr(
  constant_exprt &dest,
  const constant_exprt &expr)
{
  if(dest.type()!=expr.type())
    return true;

  const irep_idt &type_id=dest.type().id();

  if(
    type_id == ID_integer || type_id == ID_natural ||
    type_id == ID_unsignedbv || type_id == ID_signedbv)
  {
    mp_integer a, b;
    if(!to_integer(dest, a) && !to_integer(expr, b))
    {
      dest = from_integer(a + b, dest.type());
      return false;
    }
  }
  else if(type_id==ID_rational)
  {
    rationalt a, b;
    if(!to_rational(dest, a) && !to_rational(expr, b))
    {
      dest=from_rational(a+b);
      return false;
    }
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt f(dest);
    f += fixedbvt(expr);
    dest = f.to_expr();
    return false;
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt f(dest);
    f += ieee_floatt(expr);
    dest=f.to_expr();
    return false;
  }

  return true;
}

//! produce a product of two expressions of the same type
//! \return 'false' iff this was successful
static bool mul_expr(
  constant_exprt &dest,
  const constant_exprt &expr)
{
  if(dest.type()!=expr.type())
    return true;

  const irep_idt &type_id=dest.type().id();

  if(
    type_id == ID_integer || type_id == ID_natural ||
    type_id == ID_unsignedbv || type_id == ID_signedbv)
  {
    mp_integer a, b;
    if(!to_integer(dest, a) && !to_integer(expr, b))
    {
      dest = from_integer(a * b, dest.type());
      return false;
    }
  }
  else if(type_id==ID_rational)
  {
    rationalt a, b;
    if(!to_rational(dest, a) && !to_rational(expr, b))
    {
      dest=from_rational(a*b);
      return false;
    }
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt f(to_constant_expr(dest));
    f*=fixedbvt(to_constant_expr(expr));
    dest=f.to_expr();
    return false;
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt f(to_constant_expr(dest));
    f*=ieee_floatt(to_constant_expr(expr));
    dest=f.to_expr();
    return false;
  }

  return true;
}

simplify_exprt::resultt<> simplify_exprt::simplify_mult(const mult_exprt &expr)
{
  // check to see if it is a number type
  if(!is_number(expr.type()))
    return unchanged(expr);

  // vector of operands
  exprt::operandst new_operands = expr.operands();

  // result of the simplification
  bool no_change = true;

  // position of the constant
  exprt::operandst::iterator constant;

  // true if we have found a constant
  bool constant_found = false;

  optionalt<typet> c_sizeof_type;

  // scan all the operands
  for(exprt::operandst::iterator it = new_operands.begin();
      it != new_operands.end();)
  {
    // if one of the operands is not a number return
    if(!is_number(it->type()))
      return unchanged(expr);

    // if one of the operands is zero the result is zero
    // note: not true on IEEE floating point arithmetic
    if(it->is_zero() &&
       it->type().id()!=ID_floatbv)
    {
      return from_integer(0, expr.type());
    }

    // true if the given operand has to be erased
    bool do_erase = false;

    // if this is a constant of the same time as the result
    if(it->is_constant() && it->type()==expr.type())
    {
      // preserve the sizeof type annotation
      if(!c_sizeof_type.has_value())
      {
        const typet &sizeof_type =
          static_cast<const typet &>(it->find(ID_C_c_sizeof_type));
        if(sizeof_type.is_not_nil())
          c_sizeof_type = sizeof_type;
      }

      if(constant_found)
      {
        // update the constant factor
        if(!mul_expr(to_constant_expr(*constant), to_constant_expr(*it)))
          do_erase=true;
      }
      else
      {
        // set it as the constant factor if this is the first
        constant=it;
        constant_found = true;
      }
    }

    // erase the factor if necessary
    if(do_erase)
    {
      it = new_operands.erase(it);
      no_change = false;
    }
    else
      it++; // move to the next operand
  }

  if(c_sizeof_type.has_value())
  {
    INVARIANT(
      constant_found,
      "c_sizeof_type is only set to a non-nil value "
      "if a constant has been found");
    constant->set(ID_C_c_sizeof_type, *c_sizeof_type);
  }

  if(new_operands.size() == 1)
  {
    return new_operands.front();
  }
  else
  {
    // if the constant is a one and there are other factors
    if(constant_found && constant->is_one())
    {
      // just delete it
      new_operands.erase(constant);
      no_change = false;

      if(new_operands.size() == 1)
        return new_operands.front();
    }
  }

  if(no_change)
    return unchanged(expr);
  else
  {
    exprt tmp = expr;
    tmp.operands() = std::move(new_operands);
    return std::move(tmp);
  }
}

simplify_exprt::resultt<> simplify_exprt::simplify_div(const div_exprt &expr)
{
  if(!is_number(expr.type()))
    return unchanged(expr);

  const typet &expr_type=expr.type();

  if(expr_type!=expr.op0().type() ||
     expr_type!=expr.op1().type())
  {
    return unchanged(expr);
  }

  if(expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_natural ||
     expr_type.id()==ID_integer)
  {
    const auto int_value0 = numeric_cast<mp_integer>(expr.op0());
    const auto int_value1 = numeric_cast<mp_integer>(expr.op1());

    // division by zero?
    if(int_value1.has_value() && *int_value1 == 0)
      return unchanged(expr);

    // x/1?
    if(int_value1.has_value() && *int_value1 == 1)
    {
      return expr.op0();
    }

    // 0/x?
    if(int_value0.has_value() && *int_value0 == 0)
    {
      return expr.op0();
    }

    if(int_value0.has_value() && int_value1.has_value())
    {
      mp_integer result = *int_value0 / *int_value1;
      return from_integer(result, expr_type);
    }
  }
  else if(expr_type.id()==ID_rational)
  {
    rationalt rat_value0, rat_value1;
    bool ok0, ok1;

    ok0=!to_rational(expr.op0(), rat_value0);
    ok1=!to_rational(expr.op1(), rat_value1);

    if(ok1 && rat_value1.is_zero())
      return unchanged(expr);

    if((ok1 && rat_value1.is_one()) ||
       (ok0 && rat_value0.is_zero()))
    {
      return expr.op0();
    }

    if(ok0 && ok1)
    {
      rationalt result=rat_value0/rat_value1;
      exprt tmp=from_rational(result);

      if(tmp.is_not_nil())
        return std::move(tmp);
    }
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    // division by one?
    if(expr.op1().is_constant() &&
       expr.op1().is_one())
    {
      return expr.op0();
    }

    if(expr.op0().is_constant() &&
       expr.op1().is_constant())
    {
      fixedbvt f0(to_constant_expr(expr.op0()));
      fixedbvt f1(to_constant_expr(expr.op1()));
      if(!f1.is_zero())
      {
        f0/=f1;
        return f0.to_expr();
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_mod(const mod_exprt &expr)
{
  if(!is_number(expr.type()))
    return unchanged(expr);

  if(expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_natural ||
     expr.type().id()==ID_integer)
  {
    if(expr.type()==expr.op0().type() &&
       expr.type()==expr.op1().type())
    {
      const auto int_value0 = numeric_cast<mp_integer>(expr.op0());
      const auto int_value1 = numeric_cast<mp_integer>(expr.op1());

      if(int_value1.has_value() && *int_value1 == 0)
        return unchanged(expr); // division by zero

      if(
        (int_value1.has_value() && *int_value1 == 1) ||
        (int_value0.has_value() && *int_value0 == 0))
      {
        return from_integer(0, expr.type());
      }

      if(int_value0.has_value() && int_value1.has_value())
      {
        mp_integer result = *int_value0 % *int_value1;
        return from_integer(result, expr.type());
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_plus(const plus_exprt &expr)
{
  if(!is_number(expr.type()) && expr.type().id() != ID_pointer)
    return unchanged(expr);

  bool no_change = true;

  exprt::operandst new_operands = expr.operands();

  // floating-point addition is _NOT_ associative; thus,
  // there is special case for float

  if(expr.type().id() == ID_floatbv)
  {
    // we only merge neighboring constants!
    Forall_expr(it, new_operands)
    {
      const exprt::operandst::iterator next = std::next(it);

      if(next != new_operands.end())
      {
        if(it->type()==next->type() &&
           it->is_constant() &&
           next->is_constant())
        {
          sum_expr(to_constant_expr(*it), to_constant_expr(*next));
          new_operands.erase(next);
          no_change = false;
        }
      }
    }
  }
  else
  {
    // ((T*)p+a)+b -> (T*)p+(a+b)
    if(
      expr.type().id() == ID_pointer && expr.operands().size() == 2 &&
      expr.op0().id() == ID_plus && expr.op0().type().id() == ID_pointer &&
      expr.op0().operands().size() == 2)
    {
      plus_exprt result = to_plus_expr(expr.op0());
      if(as_const(result).op0().type().id() != ID_pointer)
        result.op0().swap(result.op1());
      const exprt &op1 = as_const(result).op1();

      if(op1.id() == ID_plus)
      {
        plus_exprt new_op1 = to_plus_expr(op1);
        new_op1.add_to_operands(
          typecast_exprt::conditional_cast(expr.op1(), new_op1.op0().type()));
        result.op1() = simplify_plus(new_op1);
      }
      else
      {
        plus_exprt new_op1{
          op1, typecast_exprt::conditional_cast(expr.op1(), op1.type())};
        result.op1() = simplify_plus(new_op1);
      }

      return changed(simplify_plus(result));
    }

    // count the constants
    size_t count=0;
    forall_operands(it, expr)
      if(is_number(it->type()) && it->is_constant())
        count++;

    // merge constants?
    if(count>=2)
    {
      exprt::operandst::iterator const_sum;
      bool const_sum_set=false;

      for(auto it = new_operands.begin(); it != new_operands.end(); it++)
      {
        if(is_number(it->type()) && it->is_constant())
        {
          if(!const_sum_set)
          {
            const_sum=it;
            const_sum_set=true;
          }
          else
          {
            if(!sum_expr(to_constant_expr(*const_sum), 
                         to_constant_expr(*it)))
            {
              *it=from_integer(0, it->type());
              no_change = false;
            }
          }
        }
      }
    }

    // search for a and -a
    // first gather all the a's with -a
    typedef std::unordered_map<exprt, exprt::operandst::iterator, irep_hash>
      expr_mapt;
    expr_mapt expr_map;

    for(auto it = new_operands.begin(); it != new_operands.end(); it++)
      if(it->id() == ID_unary_minus)
      {
        expr_map.insert(std::make_pair(to_unary_minus_expr(*it).op(), it));
      }

    // now search for a
    for(auto it = new_operands.begin(); it != new_operands.end(); it++)
    {
      if(expr_map.empty())
        break;
      else if(it->id()==ID_unary_minus)
        continue;

      expr_mapt::iterator itm=expr_map.find(*it);

      if(itm!=expr_map.end())
      {
        *(itm->second)=from_integer(0, expr.type());
        *it=from_integer(0, expr.type());
        expr_map.erase(itm);
        no_change = false;
      }
    }

    // delete zeros
    // (can't do for floats, as the result of 0.0 + (-0.0)
    // need not be -0.0 in std rounding)
    for(exprt::operandst::iterator it = new_operands.begin();
        it != new_operands.end();
        /* no it++ */)
    {
      if(is_number(it->type()) && it->is_zero())
      {
        it = new_operands.erase(it);
        no_change = false;
      }
      else
        it++;
    }
  }

  if(new_operands.empty())
  {
    return from_integer(0, expr.type());
  }
  else if(new_operands.size() == 1)
  {
    return new_operands.front();
  }

  if(no_change)
    return unchanged(expr);
  else
  {
    auto tmp = expr;
    tmp.operands() = std::move(new_operands);
    return std::move(tmp);
  }
}

simplify_exprt::resultt<>
simplify_exprt::simplify_minus(const minus_exprt &expr)
{
  auto const &minus_expr = to_minus_expr(expr);
  if(!is_number(minus_expr.type()) && minus_expr.type().id() != ID_pointer)
    return unchanged(expr);

  const exprt::operandst &operands = minus_expr.operands();

  if(
    is_number(minus_expr.type()) && is_number(operands[0].type()) &&
    is_number(operands[1].type()))
  {
    // rewrite "a-b" to "a+(-b)"
    unary_minus_exprt rhs_negated(operands[1]);
    plus_exprt plus_expr(operands[0], simplify_unary_minus(rhs_negated));
    return changed(simplify_plus(plus_expr));
  }
  else if(
    minus_expr.type().id() == ID_pointer &&
    operands[0].type().id() == ID_pointer && is_number(operands[1].type()))
  {
    // pointer arithmetic: rewrite "p-i" to "p+(-i)"
    unary_minus_exprt negated_pointer_offset(operands[1]);

    plus_exprt pointer_offset_expr(
      operands[0], simplify_unary_minus(negated_pointer_offset));
    return changed(simplify_plus(pointer_offset_expr));
  }
  else if(
    is_number(minus_expr.type()) && operands[0].type().id() == ID_pointer &&
    operands[1].type().id() == ID_pointer)
  {
    // pointer arithmetic: rewrite "p-p" to "0"

    if(operands[0]==operands[1])
      return from_integer(0, minus_expr.type());
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_bitwise(const multi_ary_exprt &expr)
{
  if(!is_bitvector_type(expr.type()))
    return unchanged(expr);

  // check if these are really boolean
  if(expr.type().id()!=ID_bool)
  {
    bool all_bool=true;

    forall_operands(it, expr)
    {
      if(
        it->id() == ID_typecast &&
        to_typecast_expr(*it).op().type().id() == ID_bool)
      {
      }
      else if(it->is_zero() || it->is_one())
      {
      }
      else
        all_bool=false;
    }

    if(all_bool)
    {
      // re-write to boolean+typecast
      exprt new_expr=expr;

      if(expr.id()==ID_bitand)
        new_expr.id(ID_and);
      else if(expr.id()==ID_bitor)
        new_expr.id(ID_or);
      else if(expr.id()==ID_bitxor)
        new_expr.id(ID_xor);
      else
        UNREACHABLE;

      Forall_operands(it, new_expr)
      {
        if(it->id()==ID_typecast)
          *it = to_typecast_expr(*it).op();
        else if(it->is_zero())
          *it=false_exprt();
        else if(it->is_one())
          *it=true_exprt();
      }

      new_expr.type()=bool_typet();
      new_expr = simplify_boolean(new_expr);

      return changed(simplify_typecast(typecast_exprt(new_expr, expr.type())));
    }
  }

  bool no_change = true;
  auto new_expr = expr;

  // try to merge constants

  const std::size_t width = to_bitvector_type(expr.type()).get_width();

  while(new_expr.operands().size() >= 2)
  {
    if(!new_expr.op0().is_constant())
      break;

    if(!new_expr.op1().is_constant())
      break;

    if(new_expr.op0().type() != new_expr.type())
      break;

    if(new_expr.op1().type() != new_expr.type())
      break;

    const auto &a_val = to_constant_expr(new_expr.op0()).get_value();
    const auto &b_val = to_constant_expr(new_expr.op1()).get_value();

    std::function<bool(bool, bool)> f;

    if(new_expr.id() == ID_bitand)
      f = [](bool a, bool b) { return a && b; };
    else if(new_expr.id() == ID_bitor)
      f = [](bool a, bool b) { return a || b; };
    else if(new_expr.id() == ID_bitxor)
      f = [](bool a, bool b) { return a != b; };
    else
      UNREACHABLE;

    const irep_idt new_value =
      make_bvrep(width, [&a_val, &b_val, &width, &f](std::size_t i) {
        return f(
          get_bvrep_bit(a_val, width, i), get_bvrep_bit(b_val, width, i));
      });

    constant_exprt new_op(new_value, expr.type());

    // erase first operand
    new_expr.operands().erase(new_expr.operands().begin());
    new_expr.op0().swap(new_op);

    no_change = false;
  }

  // now erase 'all zeros' out of bitor, bitxor

  if(new_expr.id() == ID_bitor || new_expr.id() == ID_bitxor)
  {
    for(exprt::operandst::iterator it = new_expr.operands().begin();
        it != new_expr.operands().end();) // no it++
    {
      if(it->is_zero() && new_expr.operands().size() > 1)
      {
        it = new_expr.operands().erase(it);
        no_change = false;
      }
      else if(
        it->is_constant() && it->type().id() == ID_bv &&
        to_constant_expr(*it).value_is_zero_string() &&
        new_expr.operands().size() > 1)
      {
        it = new_expr.operands().erase(it);
        no_change = false;
      }
      else
        it++;
    }
  }

  // now erase 'all ones' out of bitand

  if(new_expr.id() == ID_bitand)
  {
    const auto all_ones = power(2, width) - 1;
    for(exprt::operandst::iterator it = new_expr.operands().begin();
        it != new_expr.operands().end();) // no it++
    {
      if(
        it->is_constant() &&
        bvrep2integer(to_constant_expr(*it).get_value(), width, false) ==
          all_ones &&
        new_expr.operands().size() > 1)
      {
        it = new_expr.operands().erase(it);
        no_change = false;
      }
      else
        it++;
    }
  }

  // two operands that are syntactically the same

  if(new_expr.operands().size() == 2 && new_expr.op0() == new_expr.op1())
  {
    if(new_expr.id() == ID_bitand || new_expr.id() == ID_bitor)
    {
      return new_expr.op0();
    }
    else if(new_expr.id() == ID_bitxor)
    {
      return constant_exprt(integer2bvrep(0, width), new_expr.type());
    }
  }

  if(new_expr.operands().size() == 1)
    return new_expr.op0();

  if(no_change)
    return unchanged(expr);
  else
    return std::move(new_expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_extractbit(const extractbit_exprt &expr)
{
  const typet &src_type = expr.src().type();

  if(!is_bitvector_type(src_type))
    return unchanged(expr);

  const std::size_t src_bit_width = to_bitvector_type(src_type).get_width();

  const auto index_converted_to_int = numeric_cast<mp_integer>(expr.index());
  if(
    !index_converted_to_int.has_value() || *index_converted_to_int < 0 ||
    *index_converted_to_int >= src_bit_width)
  {
    return unchanged(expr);
  }

  if(!expr.src().is_constant())
    return unchanged(expr);

  const bool bit = get_bvrep_bit(
    to_constant_expr(expr.src()).get_value(),
    src_bit_width,
    numeric_cast_v<std::size_t>(*index_converted_to_int));

  return make_boolean_expr(bit);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_concatenation(const concatenation_exprt &expr)
{
  bool no_change = true;

  concatenation_exprt new_expr = expr;

  if(is_bitvector_type(new_expr.type()))
  {
    // first, turn bool into bvec[1]
    Forall_operands(it, new_expr)
    {
      exprt &op=*it;
      if(op.is_true() || op.is_false())
      {
        const bool value = op.is_true();
        op = from_integer(value, unsignedbv_typet(1));
        no_change = false;
      }
    }

    // search for neighboring constants to merge
    size_t i=0;

    while(i < new_expr.operands().size() - 1)
    {
      exprt &opi = new_expr.operands()[i];
      exprt &opn = new_expr.operands()[i + 1];

      if(opi.is_constant() &&
         opn.is_constant() &&
         is_bitvector_type(opi.type()) &&
         is_bitvector_type(opn.type()))
      {
        // merge!
        const auto &value_i = to_constant_expr(opi).get_value();
        const auto &value_n = to_constant_expr(opn).get_value();
        const auto width_i = to_bitvector_type(opi.type()).get_width();
        const auto width_n = to_bitvector_type(opn.type()).get_width();
        const auto new_width = width_i + width_n;

        const auto new_value = make_bvrep(
          new_width, [&value_i, &value_n, width_i, width_n](std::size_t x) {
            return x < width_n ? get_bvrep_bit(value_n, width_n, x)
                               : get_bvrep_bit(value_i, width_i, x - width_n);
          });

        to_constant_expr(opi).set_value(new_value);
        to_bitvector_type(opi.type()).set_width(new_width);
        // erase opn
        new_expr.operands().erase(new_expr.operands().begin() + i + 1);
        no_change = false;
      }
      else
        i++;
    }
  }
  else if(new_expr.type().id() == ID_verilog_unsignedbv)
  {
    // search for neighboring constants to merge
    size_t i=0;

    while(i < new_expr.operands().size() - 1)
    {
      exprt &opi = new_expr.operands()[i];
      exprt &opn = new_expr.operands()[i + 1];

      if(opi.is_constant() &&
         opn.is_constant() &&
         (opi.type().id()==ID_verilog_unsignedbv ||
          is_bitvector_type(opi.type())) &&
         (opn.type().id()==ID_verilog_unsignedbv ||
          is_bitvector_type(opn.type())))
      {
        // merge!
        const std::string new_value=
          opi.get_string(ID_value)+opn.get_string(ID_value);
        opi.set(ID_value, new_value);
        to_bitvector_type(opi.type()).set_width(new_value.size());
        opi.type().id(ID_verilog_unsignedbv);
        // erase opn
        new_expr.operands().erase(new_expr.operands().begin() + i + 1);
        no_change = false;
      }
      else
        i++;
    }
  }

  // { x } = x
  if(
    new_expr.operands().size() == 1 && new_expr.op0().type() == new_expr.type())
  {
    return new_expr.op0();
  }

  if(no_change)
    return unchanged(expr);
  else
    return std::move(new_expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_shifts(const shift_exprt &expr)
{
  if(!is_bitvector_type(expr.type()))
    return unchanged(expr);

  const auto distance = numeric_cast<mp_integer>(expr.distance());

  if(!distance.has_value())
    return unchanged(expr);

  if(*distance == 0)
    return expr.op();

  auto value = numeric_cast<mp_integer>(expr.op());

  if(
    !value.has_value() && expr.op().type().id() == ID_bv &&
    expr.op().id() == ID_constant)
  {
    const std::size_t width = to_bitvector_type(expr.op().type()).get_width();
    value =
      bvrep2integer(to_constant_expr(expr.op()).get_value(), width, false);
  }

  if(!value.has_value())
    return unchanged(expr);

  if(
    expr.op().type().id() == ID_unsignedbv ||
    expr.op().type().id() == ID_signedbv || expr.op().type().id() == ID_bv)
  {
    const std::size_t width = to_bitvector_type(expr.op().type()).get_width();

    if(expr.id()==ID_lshr)
    {
      // this is to guard against large values of distance
      if(*distance >= width)
      {
        return from_integer(0, expr.type());
      }
      else if(*distance >= 0)
      {
        if(*value < 0)
          *value += power(2, width);
        *value /= power(2, *distance);
        return from_integer(*value, expr.type());
      }
    }
    else if(expr.id()==ID_ashr)
    {
      if(*distance >= 0)
      {
        // this is to simulate an arithmetic right shift
        mp_integer new_value = *value >> *distance;
        return from_integer(new_value, expr.type());
      }
    }
    else if(expr.id()==ID_shl)
    {
      // this is to guard against large values of distance
      if(*distance >= width)
      {
        return from_integer(0, expr.type());
      }
      else if(*distance >= 0)
      {
        *value *= power(2, *distance);
        return from_integer(*value, expr.type());
      }
    }
  }
  else if(
    expr.op().type().id() == ID_integer || expr.op().type().id() == ID_natural)
  {
    if(expr.id()==ID_lshr)
    {
      if(*distance >= 0)
      {
        *value /= power(2, *distance);
        return from_integer(*value, expr.type());
      }
    }
    else if(expr.id()==ID_ashr)
    {
      // this is to simulate an arithmetic right shift
      if(*distance >= 0)
      {
        mp_integer new_value = *value / power(2, *distance);
        if(*value < 0 && new_value == 0)
          new_value=-1;

        return from_integer(new_value, expr.type());
      }
    }
    else if(expr.id()==ID_shl)
    {
      if(*distance >= 0)
      {
        *value *= power(2, *distance);
        return from_integer(*value, expr.type());
      }
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_power(const binary_exprt &expr)
{
  if(!is_number(expr.type()))
    return unchanged(expr);

  const auto base = numeric_cast<mp_integer>(expr.op0());
  const auto exponent = numeric_cast<mp_integer>(expr.op1());

  if(!base.has_value())
    return unchanged(expr);

  if(!exponent.has_value())
    return unchanged(expr);

  mp_integer result = power(*base, *exponent);

  return from_integer(result, expr.type());
}

/// Simplifies extracting of bits from a constant.
simplify_exprt::resultt<>
simplify_exprt::simplify_extractbits(const extractbits_exprt &expr)
{
  const typet &op0_type = expr.src().type();

  if(!is_bitvector_type(op0_type) &&
     !is_bitvector_type(expr.type()))
  {
    return unchanged(expr);
  }

  const auto start = numeric_cast<mp_integer>(expr.upper());
  const auto end = numeric_cast<mp_integer>(expr.lower());

  if(!start.has_value())
    return unchanged(expr);

  if(!end.has_value())
    return unchanged(expr);

  const auto width = pointer_offset_bits(op0_type, ns);

  if(!width.has_value())
    return unchanged(expr);

  if(*start < 0 || *start >= (*width) || *end < 0 || *end >= (*width))
    return unchanged(expr);

  DATA_INVARIANT(*start >= *end, "extractbits must have upper() >= lower()");

  if(expr.src().is_constant())
  {
    const auto svalue = expr2bits(expr.src(), true, ns);

    if(!svalue.has_value() || svalue->size() != *width)
      return unchanged(expr);

    std::string extracted_value = svalue->substr(
      numeric_cast_v<std::size_t>(*end),
      numeric_cast_v<std::size_t>(*start - *end + 1));

    auto result = bits2expr(extracted_value, expr.type(), true, ns);
    if(!result.has_value())
      return unchanged(expr);

    return std::move(*result);
  }
  else if(expr.src().id() == ID_concatenation)
  {
    // the most-significant bit comes first in an concatenation_exprt, hence we
    // count down
    mp_integer offset = *width;

    forall_operands(it, expr.src())
    {
      auto op_width = pointer_offset_bits(it->type(), ns);

      if(!op_width.has_value() || *op_width <= 0)
        return unchanged(expr);

      if(*start + 1 == offset && *end + *op_width == offset)
      {
        exprt tmp = *it;
        if(tmp.type() != expr.type())
          return unchanged(expr);

        return std::move(tmp);
      }

      offset -= *op_width;
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_unary_plus(const unary_plus_exprt &expr)
{
  // simply remove, this is always 'nop'
  return expr.op();
}

simplify_exprt::resultt<>
simplify_exprt::simplify_unary_minus(const unary_minus_exprt &expr)
{
  if(!is_number(expr.type()))
    return unchanged(expr);

  const exprt &operand = expr.op();

  if(expr.type()!=operand.type())
    return unchanged(expr);

  if(operand.id()==ID_unary_minus)
  {
    // cancel out "-(-x)" to "x"
    if(!is_number(to_unary_minus_expr(operand).op().type()))
      return unchanged(expr);

    return to_unary_minus_expr(operand).op();
  }
  else if(operand.id()==ID_constant)
  {
    const irep_idt &type_id=expr.type().id();
    const auto &constant_expr = to_constant_expr(operand);

    if(type_id==ID_integer ||
       type_id==ID_signedbv ||
       type_id==ID_unsignedbv)
    {
      const auto int_value = numeric_cast<mp_integer>(constant_expr);

      if(!int_value.has_value())
        return unchanged(expr);

      return from_integer(-*int_value, expr.type());
    }
    else if(type_id==ID_rational)
    {
      rationalt r;
      if(to_rational(constant_expr, r))
        return unchanged(expr);

      return from_rational(-r);
    }
    else if(type_id==ID_fixedbv)
    {
      fixedbvt f(constant_expr);
      f.negate();
      return f.to_expr();
    }
    else if(type_id==ID_floatbv)
    {
      ieee_floatt f(constant_expr);
      f.negate();
      return f.to_expr();
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_bitnot(const bitnot_exprt &expr)
{
  const exprt &op = expr.op();

  const auto &type = expr.type();

  if(
    type.id() == ID_bv || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv)
  {
    const auto width = to_bitvector_type(type).get_width();

    if(op.type() == type)
    {
      if(op.id()==ID_constant)
      {
        const auto &value = to_constant_expr(op).get_value();
        const auto new_value =
          make_bvrep(width, [&value, &width](std::size_t i) {
            return !get_bvrep_bit(value, width, i);
          });
        return constant_exprt(new_value, op.type());
      }
    }
  }

  return unchanged(expr);
}

/// simplifies inequalities !=, <=, <, >=, >, and also ==
simplify_exprt::resultt<>
simplify_exprt::simplify_inequality(const binary_relation_exprt &expr)
{
  if(expr.type().id()!=ID_bool)
    return unchanged(expr);

  exprt tmp0=expr.op0();
  exprt tmp1=expr.op1();

  // types must match
  if(tmp0.type() != tmp1.type())
    return unchanged(expr);

  // if rhs is ID_if (and lhs is not), swap operands for == and !=
  if((expr.id()==ID_equal || expr.id()==ID_notequal) &&
     tmp0.id()!=ID_if &&
     tmp1.id()==ID_if)
  {
    auto new_expr = expr;
    new_expr.op0().swap(new_expr.op1());
    return changed(simplify_inequality(new_expr)); // recursive call
  }

  if(tmp0.id()==ID_if && tmp0.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() =
      simplify_inequality(to_binary_relation_expr(if_expr.true_case()));
    if_expr.false_case() =
      simplify_inequality(to_binary_relation_expr(if_expr.false_case()));
    return changed(simplify_if(if_expr));
  }

  // see if we are comparing pointers that are address_of
  if(
    skip_typecast(tmp0).id() == ID_address_of &&
    skip_typecast(tmp1).id() == ID_address_of &&
    (expr.id() == ID_equal || expr.id() == ID_notequal))
  {
    return simplify_inequality_address_of(expr);
  }

  if(tmp0.id()==ID_pointer_object &&
     tmp1.id()==ID_pointer_object &&
     (expr.id()==ID_equal || expr.id()==ID_notequal))
  {
    return simplify_inequality_pointer_object(expr);
  }

  if(tmp0.type().id()==ID_c_enum_tag)
    tmp0.type()=ns.follow_tag(to_c_enum_tag_type(tmp0.type()));

  if(tmp1.type().id()==ID_c_enum_tag)
    tmp1.type()=ns.follow_tag(to_c_enum_tag_type(tmp1.type()));

  const bool tmp0_const = tmp0.is_constant();
  const bool tmp1_const = tmp1.is_constant();

  // are _both_ constant?
  if(tmp0_const && tmp1_const)
  {
    return simplify_inequality_both_constant(expr);
  }
  else if(tmp0_const)
  {
    // we want the constant on the RHS

    binary_relation_exprt new_expr = expr;

    if(expr.id()==ID_ge)
      new_expr.id(ID_le);
    else if(expr.id()==ID_le)
      new_expr.id(ID_ge);
    else if(expr.id()==ID_gt)
      new_expr.id(ID_lt);
    else if(expr.id()==ID_lt)
      new_expr.id(ID_gt);

    new_expr.op0().swap(new_expr.op1());

    // RHS is constant, LHS is not
    return changed(simplify_inequality_rhs_is_constant(new_expr));
  }
  else if(tmp1_const)
  {
    // RHS is constant, LHS is not
    return simplify_inequality_rhs_is_constant(expr);
  }
  else
  {
    // both are not constant
    return simplify_inequality_no_constant(expr);
  }
}

/// simplifies inequalities for the case in which both sides
/// of the inequality are constants
simplify_exprt::resultt<> simplify_exprt::simplify_inequality_both_constant(
  const binary_relation_exprt &expr)
{
  exprt tmp0 = expr.op0();
  exprt tmp1 = expr.op1();

  if(tmp0.type().id() == ID_c_enum_tag)
    tmp0.type() = ns.follow_tag(to_c_enum_tag_type(tmp0.type()));

  if(tmp1.type().id() == ID_c_enum_tag)
    tmp1.type() = ns.follow_tag(to_c_enum_tag_type(tmp1.type()));

  const auto &tmp0_const = to_constant_expr(tmp0);
  const auto &tmp1_const = to_constant_expr(tmp1);

  if(expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    // two constants compare equal when there values (as strings) are the same
    // or both of them are pointers and both represent NULL in some way
    bool equal = (tmp0_const.get_value() == tmp1_const.get_value());
    if(
      !equal && tmp0_const.type().id() == ID_pointer &&
      tmp1_const.type().id() == ID_pointer)
    {
      if(
        !config.ansi_c.NULL_is_zero && (tmp0_const.get_value() == ID_NULL ||
                                        tmp1_const.get_value() == ID_NULL))
      {
        // if NULL is not zero on this platform, we really don't know what it
        // is and therefore cannot simplify
        return unchanged(expr);
      }
      equal = tmp0_const.is_zero() && tmp1_const.is_zero();
    }
    return make_boolean_expr(expr.id() == ID_equal ? equal : !equal);
  }

  if(tmp0.type().id() == ID_fixedbv)
  {
    fixedbvt f0(tmp0_const);
    fixedbvt f1(tmp1_const);

    if(expr.id() == ID_ge)
      return make_boolean_expr(f0 >= f1);
    else if(expr.id() == ID_le)
      return make_boolean_expr(f0 <= f1);
    else if(expr.id() == ID_gt)
      return make_boolean_expr(f0 > f1);
    else if(expr.id() == ID_lt)
      return make_boolean_expr(f0 < f1);
    else
      UNREACHABLE;
  }
  else if(tmp0.type().id() == ID_floatbv)
  {
    ieee_floatt f0(tmp0_const);
    ieee_floatt f1(tmp1_const);

    if(expr.id() == ID_ge)
      return make_boolean_expr(f0 >= f1);
    else if(expr.id() == ID_le)
      return make_boolean_expr(f0 <= f1);
    else if(expr.id() == ID_gt)
      return make_boolean_expr(f0 > f1);
    else if(expr.id() == ID_lt)
      return make_boolean_expr(f0 < f1);
    else
      UNREACHABLE;
  }
  else if(tmp0.type().id() == ID_rational)
  {
    rationalt r0, r1;

    if(to_rational(tmp0, r0))
      return unchanged(expr);

    if(to_rational(tmp1, r1))
      return unchanged(expr);

    if(expr.id() == ID_ge)
      return make_boolean_expr(r0 >= r1);
    else if(expr.id() == ID_le)
      return make_boolean_expr(r0 <= r1);
    else if(expr.id() == ID_gt)
      return make_boolean_expr(r0 > r1);
    else if(expr.id() == ID_lt)
      return make_boolean_expr(r0 < r1);
    else
      UNREACHABLE;
  }
  else
  {
    const auto v0 = numeric_cast<mp_integer>(tmp0_const);

    if(!v0.has_value())
      return unchanged(expr);

    const auto v1 = numeric_cast<mp_integer>(tmp1_const);

    if(!v1.has_value())
      return unchanged(expr);

    if(expr.id() == ID_ge)
      return make_boolean_expr(*v0 >= *v1);
    else if(expr.id() == ID_le)
      return make_boolean_expr(*v0 <= *v1);
    else if(expr.id() == ID_gt)
      return make_boolean_expr(*v0 > *v1);
    else if(expr.id() == ID_lt)
      return make_boolean_expr(*v0 < *v1);
    else
      UNREACHABLE;
  }
}

static bool eliminate_common_addends(exprt &op0, exprt &op1)
{
  // we can't eliminate zeros
  if(op0.is_zero() ||
     op1.is_zero() ||
     (op0.is_constant() &&
      to_constant_expr(op0).get_value()==ID_NULL) ||
     (op1.is_constant() &&
      to_constant_expr(op1).get_value()==ID_NULL))
    return true;

  if(op0.id()==ID_plus)
  {
    bool no_change = true;

    Forall_operands(it, op0)
      if(!eliminate_common_addends(*it, op1))
        no_change = false;

    return no_change;
  }
  else if(op1.id()==ID_plus)
  {
    bool no_change = true;

    Forall_operands(it, op1)
      if(!eliminate_common_addends(op0, *it))
        no_change = false;

    return no_change;
  }
  else if(op0==op1)
  {
    if(!op0.is_zero() &&
       op0.type().id()!=ID_complex)
    {
      // elimination!
      op0=from_integer(0, op0.type());
      op1=from_integer(0, op1.type());
      return false;
    }
  }

  return true;
}

simplify_exprt::resultt<> simplify_exprt::simplify_inequality_no_constant(
  const binary_relation_exprt &expr)
{
  // pretty much all of the simplifications below are unsound
  // for IEEE float because of NaN!

  if(expr.op0().type().id() == ID_floatbv)
    return unchanged(expr);

  // simplifications below require same-object, which we don't check for
  if(
    expr.op0().type().id() == ID_pointer && expr.id() != ID_equal &&
    expr.id() != ID_notequal)
  {
    return unchanged(expr);
  }

  // eliminate strict inequalities
  if(expr.id()==ID_notequal)
  {
    auto new_rel_expr = expr;
    new_rel_expr.id(ID_equal);
    auto new_expr = simplify_inequality_no_constant(new_rel_expr);
    return changed(simplify_not(not_exprt(new_expr)));
  }
  else if(expr.id()==ID_gt)
  {
    auto new_rel_expr = expr;
    new_rel_expr.id(ID_ge);
    // swap operands
    new_rel_expr.lhs().swap(new_rel_expr.rhs());
    auto new_expr = simplify_inequality_no_constant(new_rel_expr);
    return changed(simplify_not(not_exprt(new_expr)));
  }
  else if(expr.id()==ID_lt)
  {
    auto new_rel_expr = expr;
    new_rel_expr.id(ID_ge);
    auto new_expr = simplify_inequality_no_constant(new_rel_expr);
    return changed(simplify_not(not_exprt(new_expr)));
  }
  else if(expr.id()==ID_le)
  {
    auto new_rel_expr = expr;
    new_rel_expr.id(ID_ge);
    // swap operands
    new_rel_expr.lhs().swap(new_rel_expr.rhs());
    return changed(simplify_inequality_no_constant(new_rel_expr));
  }

  // now we only have >=, =

  INVARIANT(
    expr.id() == ID_ge || expr.id() == ID_equal,
    "we previously converted all other cases to >= or ==");

  // syntactically equal?

  if(expr.op0() == expr.op1())
    return true_exprt();

  // See if we can eliminate common addends on both sides.
  // On bit-vectors, this is only sound on '='.
  if(expr.id()==ID_equal)
  {
    auto new_expr = to_equal_expr(expr);
    if(!eliminate_common_addends(new_expr.lhs(), new_expr.rhs()))
    {
      // remove zeros
      new_expr.lhs() = simplify_node(new_expr.lhs());
      new_expr.rhs() = simplify_node(new_expr.rhs());
      return changed(simplify_inequality(new_expr)); // recursive call
    }
  }

  return unchanged(expr);
}

/// \par expr: an inequality where the RHS is a constant
/// and the LHS is not
simplify_exprt::resultt<> simplify_exprt::simplify_inequality_rhs_is_constant(
  const binary_relation_exprt &expr)
{
  // the constant is always on the RHS
  PRECONDITION(expr.op1().is_constant());

  if(expr.op0().id()==ID_if && expr.op0().operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() =
      simplify_inequality(to_binary_relation_expr(if_expr.true_case()));
    if_expr.false_case() =
      simplify_inequality(to_binary_relation_expr(if_expr.false_case()));
    return changed(simplify_if(if_expr));
  }

  // do we deal with pointers?
  if(expr.op1().type().id()==ID_pointer)
  {
    if(expr.id()==ID_notequal)
    {
      auto new_rel_expr = expr;
      new_rel_expr.id(ID_equal);
      auto new_expr = simplify_inequality_rhs_is_constant(new_rel_expr);
      return changed(simplify_not(not_exprt(new_expr)));
    }

    // very special case for pointers
    if(expr.id()==ID_equal &&
       expr.op1().is_constant() &&
       expr.op1().get(ID_value)==ID_NULL)
    {
      // the address of an object is never NULL

      if(expr.op0().id() == ID_address_of)
      {
        const auto &object = to_address_of_expr(expr.op0()).object();

        if(
          object.id() == ID_symbol || object.id() == ID_dynamic_object ||
          object.id() == ID_member || object.id() == ID_index ||
          object.id() == ID_string_constant)
        {
          return false_exprt();
        }
      }
      else if(
        expr.op0().id() == ID_typecast &&
        expr.op0().type().id() == ID_pointer &&
        to_typecast_expr(expr.op0()).op().id() == ID_address_of)
      {
        const auto &object =
          to_address_of_expr(to_typecast_expr(expr.op0()).op()).object();

        if(
          object.id() == ID_symbol || object.id() == ID_dynamic_object ||
          object.id() == ID_member || object.id() == ID_index ||
          object.id() == ID_string_constant)
        {
          return false_exprt();
        }
      }
      else if(
        expr.op0().id() == ID_typecast && expr.op0().type().id() == ID_pointer)
      {
        exprt op = to_typecast_expr(expr.op0()).op();
        if(
          op.type().id() != ID_pointer &&
          (!config.ansi_c.NULL_is_zero || !is_number(op.type()) ||
           op.type().id() == ID_complex))
        {
          return unchanged(expr);
        }

        // (type)ptr == NULL -> ptr == NULL
        // note that 'ptr' may be an integer
        auto new_expr = expr;
        new_expr.op0().swap(op);
        if(new_expr.op0().type().id() != ID_pointer)
          new_expr.op1() = from_integer(0, new_expr.op0().type());
        else
          new_expr.op1().type() = new_expr.op0().type();
        return changed(simplify_inequality(new_expr)); // do again!
      }
    }

    // all we are doing with pointers
    return unchanged(expr);
  }

  // is it a separation predicate?

  if(expr.op0().id()==ID_plus)
  {
    // see if there is a constant in the sum

    if(expr.id()==ID_equal || expr.id()==ID_notequal)
    {
      mp_integer constant=0;
      bool op_changed = false;
      auto new_expr = expr;

      Forall_operands(it, new_expr.op0())
      {
        if(it->is_constant())
        {
          mp_integer i;
          if(!to_integer(to_constant_expr(*it), i))
          {
            constant+=i;
            *it=from_integer(0, it->type());
            op_changed = true;
          }
        }
      }

      if(op_changed)
      {
        // adjust the constant on the RHS
        mp_integer i =
          numeric_cast_v<mp_integer>(to_constant_expr(new_expr.op1()));
        i-=constant;
        new_expr.op1() = from_integer(i, new_expr.op1().type());

        new_expr.op0() = simplify_plus(to_plus_expr(new_expr.op0()));
        return changed(simplify_inequality(new_expr));
      }
    }
  }

  #if 1
  // (double)value REL const ---> value rel const
  // if 'const' can be represented exactly.

  if(
    expr.op0().id() == ID_typecast && expr.op0().type().id() == ID_floatbv &&
    to_typecast_expr(expr.op0()).op().type().id() == ID_floatbv)
  {
    ieee_floatt const_val(to_constant_expr(expr.op1()));
    ieee_floatt const_val_converted=const_val;
    const_val_converted.change_spec(ieee_float_spect(
      to_floatbv_type(to_typecast_expr(expr.op0()).op().type())));
    ieee_floatt const_val_converted_back=const_val_converted;
    const_val_converted_back.change_spec(
      ieee_float_spect(to_floatbv_type(expr.op0().type())));
    if(const_val_converted_back==const_val)
    {
      auto result = expr;
      result.op0() = to_typecast_expr(expr.op0()).op();
      result.op1()=const_val_converted.to_expr();
      return std::move(result);
    }
  }
  #endif

  // is the constant zero?

  if(expr.op1().is_zero())
  {
    if(expr.id()==ID_ge &&
       expr.op0().type().id()==ID_unsignedbv)
    {
      // zero is always smaller or equal something unsigned
      return true_exprt();
    }

    auto new_expr = expr;
    exprt &operand = new_expr.op0();

    if(expr.id()==ID_equal)
    {
      // rules below do not hold for >=
      if(operand.id()==ID_unary_minus)
      {
        operand = to_unary_minus_expr(operand).op();
        return std::move(new_expr);
      }
      else if(operand.id()==ID_plus)
      {
        auto &operand_plus_expr = to_plus_expr(operand);

        // simplify a+-b=0 to a=b
        if(operand_plus_expr.operands().size() == 2)
        {
          // if we have -b+a=0, make that a+(-b)=0
          if(operand_plus_expr.op0().id() == ID_unary_minus)
            operand_plus_expr.op0().swap(operand_plus_expr.op1());

          if(operand_plus_expr.op1().id() == ID_unary_minus)
          {
            return binary_exprt(
              operand_plus_expr.op0(),
              expr.id(),
              to_unary_minus_expr(operand_plus_expr.op1()).op(),
              expr.type());
          }
        }
      }
    }
  }

  // are we comparing with a typecast from bool?
  if(
    expr.op0().id() == ID_typecast &&
    to_typecast_expr(expr.op0()).op().type().id() == ID_bool)
  {
    const auto &lhs_typecast_op = to_typecast_expr(expr.op0()).op();

    // we re-write (TYPE)boolean == 0 -> !boolean
    if(expr.op1().is_zero() && expr.id()==ID_equal)
    {
      return changed(simplify_not(not_exprt(lhs_typecast_op)));
    }

    // we re-write (TYPE)boolean != 0 -> boolean
    if(expr.op1().is_zero() && expr.id()==ID_notequal)
    {
      return lhs_typecast_op;
    }
  }

  #define NORMALISE_CONSTANT_TESTS
  #ifdef NORMALISE_CONSTANT_TESTS
  // Normalise to >= and = to improve caching and term sharing
  if(expr.op0().type().id()==ID_unsignedbv ||
     expr.op0().type().id()==ID_signedbv)
  {
    mp_integer max(to_integer_bitvector_type(expr.op0().type()).largest());

    if(expr.id()==ID_notequal)
    {
      auto new_rel_expr = expr;
      new_rel_expr.id(ID_equal);
      auto new_expr = simplify_inequality_rhs_is_constant(new_rel_expr);
      return changed(simplify_not(not_exprt(new_expr)));
    }
    else if(expr.id()==ID_gt)
    {
      mp_integer i = numeric_cast_v<mp_integer>(to_constant_expr(expr.op1()));

      if(i==max)
      {
        return false_exprt();
      }

      auto new_expr = expr;
      new_expr.id(ID_ge);
      ++i;
      new_expr.op1() = from_integer(i, new_expr.op1().type());
      return changed(simplify_inequality_rhs_is_constant(new_expr));
    }
    else if(expr.id()==ID_lt)
    {
      auto new_rel_expr = expr;
      new_rel_expr.id(ID_ge);
      auto new_expr = simplify_inequality_rhs_is_constant(new_rel_expr);
      return changed(simplify_not(not_exprt(new_expr)));
    }
    else if(expr.id()==ID_le)
    {
      mp_integer i = numeric_cast_v<mp_integer>(to_constant_expr(expr.op1()));

      if(i==max)
      {
        return true_exprt();
      }

      auto new_rel_expr = expr;
      new_rel_expr.id(ID_ge);
      ++i;
      new_rel_expr.op1() = from_integer(i, new_rel_expr.op1().type());
      auto new_expr = simplify_inequality_rhs_is_constant(new_rel_expr);
      return changed(simplify_not(not_exprt(new_expr)));
    }
  }
#endif
  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_bitreverse(const bitreverse_exprt &expr)
{
  auto const_bits_opt = expr2bits(
    expr.op(),
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN,
    ns);

  if(!const_bits_opt.has_value())
    return unchanged(expr);

  std::reverse(const_bits_opt->begin(), const_bits_opt->end());

  auto result = bits2expr(
    *const_bits_opt,
    expr.type(),
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN,
    ns);
  if(!result.has_value())
    return unchanged(expr);

  return std::move(*result);
}
