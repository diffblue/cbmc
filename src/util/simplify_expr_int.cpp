/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include <cassert>

#include "arith_tools.h"
#include "base_type.h"
#include "bv_arithmetic.h"
#include "config.h"
#include "expr_util.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "invariant.h"
#include "mathematical_types.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_expr.h"

bool simplify_exprt::simplify_bswap(bswap_exprt &expr)
{
  if(expr.type().id() == ID_unsignedbv && expr.op().is_constant())
  {
    auto bits_per_byte = expr.get_bits_per_byte();
    std::size_t width=to_bitvector_type(expr.type()).get_width();
    mp_integer value;
    to_integer(expr.op(), value);
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

    constant_exprt c = from_integer(new_value, expr.type());
    expr.swap(c);
    return false;
  }

  return true;
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

bool simplify_exprt::simplify_mult(exprt &expr)
{
  // check to see if it is a number type
  if(!is_number(expr.type()))
    return true;

  // vector of operands
  exprt::operandst &operands=expr.operands();

  // result of the simplification
  bool result = true;

  // position of the constant
  exprt::operandst::iterator constant;

  // true if we have found a constant
  bool constant_found = false;

  typet c_sizeof_type=nil_typet();

  // scan all the operands
  for(exprt::operandst::iterator it=operands.begin();
      it!=operands.end();)
  {
    // if one of the operands is not a number return
    if(!is_number(it->type()))
      return true;

    // if one of the operands is zero the result is zero
    // note: not true on IEEE floating point arithmetic
    if(it->is_zero() &&
       it->type().id()!=ID_floatbv)
    {
      expr=from_integer(0, expr.type());
      return false;
    }

    // true if the given operand has to be erased
    bool do_erase = false;

    // if this is a constant of the same time as the result
    if(it->is_constant() && it->type()==expr.type())
    {
      // preserve the sizeof type annotation
      if(c_sizeof_type.is_nil())
        c_sizeof_type=
          static_cast<const typet &>(it->find(ID_C_c_sizeof_type));

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
      it=operands.erase(it);
      result = false;
    }
    else
      it++; // move to the next operand
  }

  if(c_sizeof_type.is_not_nil())
  {
    INVARIANT(
      constant_found,
      "c_sizeof_type is only set to a non-nil value "
      "if a constant has been found");
    constant->set(ID_C_c_sizeof_type, c_sizeof_type);
  }

  if(operands.size()==1)
  {
    exprt product(operands.front());
    expr.swap(product);

    result = false;
  }
  else
  {
    // if the constant is a one and there are other factors
    if(constant_found && constant->is_one())
    {
      // just delete it
      operands.erase(constant);
      result=false;

      if(operands.size()==1)
      {
        exprt product(operands.front());
        expr.swap(product);
      }
    }
  }

  return result;
}

bool simplify_exprt::simplify_div(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  const typet &expr_type=expr.type();

  if(expr_type!=expr.op0().type() ||
     expr_type!=expr.op1().type())
    return true;

  if(expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_natural ||
     expr_type.id()==ID_integer)
  {
    mp_integer int_value0, int_value1;
    bool ok0, ok1;

    ok0=!to_integer(expr.op0(), int_value0);
    ok1=!to_integer(expr.op1(), int_value1);

    // division by zero?
    if(ok1 && int_value1==0)
      return true;

    // x/1?
    if(ok1 && int_value1==1)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    // 0/x?
    if(ok0 && int_value0==0)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      mp_integer result=int_value0/int_value1;
      exprt tmp=from_integer(result, expr_type);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_rational)
  {
    rationalt rat_value0, rat_value1;
    bool ok0, ok1;

    ok0=!to_rational(expr.op0(), rat_value0);
    ok1=!to_rational(expr.op1(), rat_value1);

    if(ok1 && rat_value1.is_zero())
      return true;

    if((ok1 && rat_value1.is_one()) ||
       (ok0 && rat_value0.is_zero()))
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      rationalt result=rat_value0/rat_value1;
      exprt tmp=from_rational(result);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    // division by one?
    if(expr.op1().is_constant() &&
       expr.op1().is_one())
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(expr.op0().is_constant() &&
       expr.op1().is_constant())
    {
      fixedbvt f0(to_constant_expr(expr.op0()));
      fixedbvt f1(to_constant_expr(expr.op1()));
      if(!f1.is_zero())
      {
        f0/=f1;
        expr=f0.to_expr();
        return false;
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_mod(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  if(expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_natural ||
     expr.type().id()==ID_integer)
  {
    if(expr.type()==expr.op0().type() &&
       expr.type()==expr.op1().type())
    {
      mp_integer int_value0, int_value1;
      bool ok0, ok1;

      ok0=!to_integer(expr.op0(), int_value0);
      ok1=!to_integer(expr.op1(), int_value1);

      if(ok1 && int_value1==0)
        return true; // division by zero

      if((ok1 && int_value1==1) ||
         (ok0 && int_value0==0))
      {
        expr=from_integer(0, expr.type());
        return false;
      }

      if(ok0 && ok1)
      {
        mp_integer result=int_value0%int_value1;
        exprt tmp=from_integer(result, expr.type());

        if(tmp.is_not_nil())
        {
          expr.swap(tmp);
          return false;
        }
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_plus(exprt &expr)
{
  auto const &plus_expr = to_plus_expr(expr);
  if(!is_number(plus_expr.type()) && plus_expr.type().id() != ID_pointer)
    return true;

  bool result=true;

  exprt::operandst &operands=expr.operands();

  // floating-point addition is _NOT_ associative; thus,
  // there is special case for float

  if(ns.follow(plus_expr.type()).id() == ID_floatbv)
  {
    // we only merge neighboring constants!
    Forall_expr(it, operands)
    {
      exprt::operandst::iterator next=it;
      next++;

      if(next!=operands.end())
      {
        if(it->type()==next->type() &&
           it->is_constant() &&
           next->is_constant())
        {
          sum_expr(to_constant_expr(*it), to_constant_expr(*next));
          operands.erase(next);
        }
      }
    }
  }
  else
  {
    // ((T*)p+a)+b -> (T*)p+(a+b)
    if(
      plus_expr.type().id() == ID_pointer && plus_expr.operands().size() == 2 &&
      plus_expr.op0().id() == ID_plus && plus_expr.op0().operands().size() == 2)
    {
      exprt op0 = plus_expr.op0();

      if(plus_expr.op0().op1().id() == ID_plus)
        op0.op1().copy_to_operands(expr.op1());
      else
        op0.op1()=plus_exprt(op0.op1(), expr.op1());

      expr.swap(op0);

      simplify_plus(expr.op1());
      simplify_plus(expr);

      return false;
    }

    // count the constants
    size_t count=0;
    forall_operands(it, plus_expr)
      if(is_number(it->type()) && it->is_constant())
        count++;

    // merge constants?
    if(count>=2)
    {
      exprt::operandst::iterator const_sum;
      bool const_sum_set=false;

      Forall_operands(it, expr)
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
              CHECK_RETURN(it->is_not_nil());
              result=false;
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

    Forall_expr(it, operands)
      if(it->id()==ID_unary_minus &&
         it->operands().size()==1)
        expr_map.insert(std::make_pair(it->op0(), it));

    // now search for a
    Forall_expr(it, operands)
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
        CHECK_RETURN(it->is_not_nil());
        expr_map.erase(itm);
        result=false;
      }
    }

    // delete zeros
    // (can't do for floats, as the result of 0.0 + (-0.0)
    // need not be -0.0 in std rounding)
    for(exprt::operandst::iterator
        it=operands.begin();
        it!=operands.end();
        /* no it++ */)
    {
      if(is_number(it->type()) && it->is_zero())
      {
        it=operands.erase(it);
        result=false;
      }
      else
        it++;
    }
  }

  if(operands.empty())
  {
    expr = from_integer(0, plus_expr.type());
    CHECK_RETURN(expr.is_not_nil());
    return false;
  }
  else if(operands.size()==1)
  {
    exprt tmp(operands.front());
    expr.swap(tmp);
    return false;
  }

  return result;
}

bool simplify_exprt::simplify_minus(exprt &expr)
{
  auto const &minus_expr = to_minus_expr(expr);
  if(!is_number(minus_expr.type()) && minus_expr.type().id() != ID_pointer)
    return true;

  const exprt::operandst &operands = minus_expr.operands();

  if(operands.size()!=2)
    return true;

  if(
    is_number(minus_expr.type()) && is_number(operands[0].type()) &&
    is_number(operands[1].type()))
  {
    // rewrite "a-b" to "a+(-b)"
    unary_minus_exprt rhs_negated(operands[1]);
    simplify_unary_minus(rhs_negated);

    plus_exprt plus_expr(operands[0], rhs_negated);
    simplify_node(plus_expr);

    expr.swap(plus_expr);
    return false;
  }
  else if(
    minus_expr.type().id() == ID_pointer &&
    operands[0].type().id() == ID_pointer && is_number(operands[1].type()))
  {
    // pointer arithmetic: rewrite "p-i" to "p+(-i)"
    unary_minus_exprt negated_pointer_offset(operands[1]);
    simplify_unary_minus(negated_pointer_offset);

    plus_exprt pointer_offset_expr(operands[0], negated_pointer_offset);
    simplify_plus(pointer_offset_expr);

    expr.swap(pointer_offset_expr);
    return false;
  }
  else if(
    is_number(minus_expr.type()) && operands[0].type().id() == ID_pointer &&
    operands[1].type().id() == ID_pointer)
  {
    // pointer arithmetic: rewrite "p-p" to "0"

    if(operands[0]==operands[1])
    {
      exprt zero = from_integer(0, minus_expr.type());
      CHECK_RETURN(zero.is_not_nil());
      expr=zero;
      return false;
    }
  }

  return true;
}

bool simplify_exprt::simplify_bitwise(exprt &expr)
{
  if(!is_bitvector_type(expr.type()))
    return true;

  // check if these are really boolean
  if(expr.type().id()!=ID_bool)
  {
    bool all_bool=true;

    forall_operands(it, expr)
    {
      if(it->id()==ID_typecast &&
         it->operands().size()==1 &&
         ns.follow(it->op0().type()).id()==ID_bool)
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
        {
          exprt tmp;
          tmp=it->op0();
          it->swap(tmp);
        }
        else if(it->is_zero())
          *it=false_exprt();
        else if(it->is_one())
          *it=true_exprt();
      }

      new_expr.type()=bool_typet();
      simplify_node(new_expr);

      new_expr.make_typecast(expr.type());
      simplify_node(new_expr);

      expr.swap(new_expr);
      return false;
    }
  }

  bool result=true;

  // try to merge constants

  const std::size_t width = to_bitvector_type(expr.type()).get_width();

  while(expr.operands().size()>=2)
  {
    if(!expr.op0().is_constant())
      break;

    if(!expr.op1().is_constant())
      break;

    if(expr.op0().type()!=expr.type())
      break;

    if(expr.op1().type()!=expr.type())
      break;

    const auto &a_val = to_constant_expr(expr.op0()).get_value();
    const auto &b_val = to_constant_expr(expr.op1()).get_value();

    std::function<bool(bool, bool)> f;

    if(expr.id()==ID_bitand)
      f = [](bool a, bool b) { return a & b; };
    else if(expr.id()==ID_bitor)
      f = [](bool a, bool b) { return a | b; };
    else if(expr.id()==ID_bitxor)
      f = [](bool a, bool b) { return a ^ b; };
    else
      UNREACHABLE;

    const irep_idt new_value =
      make_bvrep(width, [&a_val, &b_val, &width, &f](std::size_t i) {
        return f(
          get_bitvector_bit(a_val, width, i),
          get_bitvector_bit(b_val, width, i));
      });

    constant_exprt new_op(new_value, expr.type());

    // erase first operand
    expr.operands().erase(expr.operands().begin());
    expr.op0().swap(new_op);

    result=false;
  }

  // now erase 'all zeros' out of bitor, bitxor

  if(expr.id()==ID_bitor || expr.id()==ID_bitxor)
  {
    for(exprt::operandst::iterator
        it=expr.operands().begin();
        it!=expr.operands().end();
        ) // no it++
    {
      if(it->is_zero() && expr.operands().size()>1)
      {
        it=expr.operands().erase(it);
        result=false;
      }
      else
        it++;
    }
  }

  // now erase 'all ones' out of bitand

  if(expr.id()==ID_bitand)
  {
    for(exprt::operandst::iterator
        it=expr.operands().begin();
        it!=expr.operands().end();
        ) // no it++
    {
      if(
        it->is_constant() &&
        bv2integer(
          to_constant_expr(*it).get_value(), width, false) ==
          power(2, width) - 1 &&
        expr.operands().size() > 1)
      {
        it=expr.operands().erase(it);
        result=false;
      }
      else
        it++;
    }
  }

  // two operands that are syntactically the same

  if(expr.operands().size()==2 &&
     expr.op0()==expr.op1())
  {
    if(expr.id()==ID_bitand || expr.id()==ID_bitor)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }
    else if(expr.id()==ID_bitxor)
    {
      constant_exprt new_op(integer2bv(0, width), expr.type());
      expr.swap(new_op);
      return false;
    }
  }

  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  return result;
}

bool simplify_exprt::simplify_extractbit(exprt &expr)
{
  PRECONDITION(expr.id() == ID_extractbit);
  const auto &extractbit_expr = to_extractbit_expr(expr);

  const typet &src_type = extractbit_expr.src().type();

  if(!is_bitvector_type(src_type))
    return true;

  const std::size_t src_bit_width = to_bitvector_type(src_type).get_width();

  const auto index_converted_to_int =
    numeric_cast<mp_integer>(extractbit_expr.index());
  if(!index_converted_to_int.has_value())
  {
    return true;
  }
  const mp_integer index_as_int = index_converted_to_int.value();
  if(!extractbit_expr.src().is_constant())
    return true;

  if(index_as_int < 0 || index_as_int >= src_bit_width)
    return true;

  const irep_idt &src_value =
    to_constant_expr(extractbit_expr.src()).get_value();

  std::string src_value_as_string = id2string(src_value);

  if(src_value_as_string.size() != src_bit_width)
    return true;

  const bool bit =
    (src_value_as_string[src_bit_width -
                         numeric_cast_v<std::size_t>(index_as_int) - 1] == '1');

  expr.make_bool(bit);

  return false;
}

bool simplify_exprt::simplify_concatenation(exprt &expr)
{
  bool result=true;

  if(is_bitvector_type(expr.type()))
  {
    // first, turn bool into bvec[1]
    Forall_operands(it, expr)
    {
      exprt &op=*it;
      if(op.is_true() || op.is_false())
      {
        const bool value = op.is_true();
        op = from_integer(value, unsignedbv_typet(1));
        result = false;
      }
    }

    // search for neighboring constants to merge
    size_t i=0;

    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];

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
            return x < width_n
                     ? get_bitvector_bit(value_n, width_n, x)
                     : get_bitvector_bit(value_i, width_i, x - width_n);
          });

        to_constant_expr(opi).set_value(new_value);
        opi.type().set(ID_width, new_width);
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result = false;
      }
      else
        i++;
    }
  }
  else if(expr.type().id()==ID_verilog_unsignedbv)
  {
    // search for neighboring constants to merge
    size_t i=0;

    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];

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
        opi.type().set(ID_width, new_value.size());
        opi.type().id(ID_verilog_unsignedbv);
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result = false;
      }
      else
        i++;
    }
  }

  // { x } = x
  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    result=false;
  }

  return result;
}

bool simplify_exprt::simplify_shifts(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  mp_integer distance;

  if(to_integer(expr.op1(), distance))
    return true;

  if(distance==0)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  mp_integer value;

  if(to_integer(expr.op0(), value))
    return true;

  if(expr.op0().type().id()==ID_unsignedbv ||
     expr.op0().type().id()==ID_signedbv)
  {
    mp_integer width=
      string2integer(id2string(expr.op0().type().get(ID_width)));

    if(expr.id()==ID_lshr)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=from_integer(0, expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      if(distance>=0)
      {
        // this is to simulate an arithmetic right shift
        mp_integer new_value=value>>distance; // NOLINT(whitespace/operators)
        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=from_integer(0, expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_integer ||
          expr.op0().type().id()==ID_natural)
  {
    if(expr.id()==ID_lshr)
    {
      if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      // this is to simulate an arithmetic right shift
      if(distance>=0)
      {
        mp_integer new_value=value/power(2, distance);
        if(value<0 && new_value==0)
          new_value=-1;

        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_power(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  mp_integer base, exponent;

  if(to_integer(expr.op0(), base))
    return true;

  if(to_integer(expr.op1(), exponent))
    return true;

  mp_integer result=power(base, exponent);

  expr=from_integer(result, expr.type());
  return false;
}

/// Simplifies extracting of bits from a constant.
bool simplify_exprt::simplify_extractbits(extractbits_exprt &expr)
{
  const typet &op0_type = expr.src().type();

  if(!is_bitvector_type(op0_type) &&
     !is_bitvector_type(expr.type()))
    return true;

  mp_integer start, end;

  if(to_integer(expr.upper(), start))
    return true;

  if(to_integer(expr.lower(), end))
    return true;

  const auto width = pointer_offset_bits(op0_type, ns);

  if(!width.has_value())
    return true;

  if(start < 0 || start >= (*width) || end < 0 || end >= (*width))
    return true;

  DATA_INVARIANT(
    start >= end,
    "extractbits must have upper() >= lower()");

  if(expr.src().is_constant())
  {
    const irep_idt &value = to_constant_expr(expr.src()).get_value();

    if(value.size() != *width)
      return true;

    std::string svalue=id2string(value);

    std::string extracted_value = svalue.substr(
      integer2size_t(*width - start - 1), integer2size_t(start - end + 1));

    constant_exprt result(extracted_value, expr.type());
    expr.swap(result);

    return false;
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
        return true;

      if(start + 1 == offset && end + *op_width == offset)
      {
        exprt tmp = *it;
        if(tmp.type() != expr.type())
          return true;

        expr.swap(tmp);
        return false;
      }

      offset -= *op_width;
    }
  }

  return true;
}

bool simplify_exprt::simplify_unary_plus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  // simply remove, this is always 'nop'
  expr=expr.op0();
  return false;
}

bool simplify_exprt::simplify_unary_minus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(!is_number(expr.type()))
    return true;

  exprt &operand=expr.op0();

  if(expr.type()!=operand.type())
    return true;

  if(operand.id()==ID_unary_minus)
  {
    // cancel out "-(-x)" to "x"
    if(operand.operands().size()!=1)
      return true;

    if(!is_number(operand.op0().type()))
      return true;

    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.swap(tmp);
    return false;
  }
  else if(operand.id()==ID_constant)
  {
    const irep_idt &type_id=expr.type().id();

    if(type_id==ID_integer ||
       type_id==ID_signedbv ||
       type_id==ID_unsignedbv)
    {
      mp_integer int_value;

      if(to_integer(expr.op0(), int_value))
        return true;

      exprt tmp=from_integer(-int_value, expr.type());

      if(tmp.is_nil())
        return true;

      expr.swap(tmp);

      return false;
    }
    else if(type_id==ID_rational)
    {
      rationalt r;
      if(to_rational(expr.op0(), r))
        return true;

      expr=from_rational(-r);
      return false;
    }
    else if(type_id==ID_fixedbv)
    {
      fixedbvt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
    else if(type_id==ID_floatbv)
    {
      ieee_floatt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
  }

  return true;
}

bool simplify_exprt::simplify_bitnot(exprt &expr)
{
  if(!expr.has_operands())
    return true;

  exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    return true;

  exprt &op=operands.front();

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
            return !get_bitvector_bit(value, width, i);
          });
        expr = constant_exprt(new_value, op.type());
        return false;
      }
    }
  }

  return true;
}

/// simplifies inequalities !=, <=, <, >=, >, and also ==
bool simplify_exprt::simplify_inequality(exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool)
    return true;

  if(operands.size()!=2)
    return true;

  exprt tmp0=expr.op0();
  exprt tmp1=expr.op1();

  // types must match
  if(!base_type_eq(tmp0.type(), tmp1.type(), ns))
    return true;

  // if rhs is ID_if (and lhs is not), swap operands for == and !=
  if((expr.id()==ID_equal || expr.id()==ID_notequal) &&
     tmp0.id()!=ID_if &&
     tmp1.id()==ID_if)
  {
    expr.op0().swap(expr.op1());
    return simplify_inequality(expr);
  }

  if(tmp0.id()==ID_if && tmp0.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    simplify_inequality(if_expr.true_case());
    simplify_inequality(if_expr.false_case());
    simplify_if(if_expr);
    expr.swap(if_expr);

    return false;
  }

  // see if we are comparing pointers that are address_of
  if((tmp0.id()==ID_address_of ||
        (tmp0.id()==ID_typecast && tmp0.op0().id()==ID_address_of)) &&
      (tmp1.id()==ID_address_of ||
       (tmp1.id()==ID_typecast && tmp1.op0().id()==ID_address_of)) &&
      (expr.id()==ID_equal || expr.id()==ID_notequal))
    return simplify_inequality_address_of(expr);

  if(tmp0.id()==ID_pointer_object &&
     tmp1.id()==ID_pointer_object &&
     (expr.id()==ID_equal || expr.id()==ID_notequal))
    return simplify_inequality_pointer_object(expr);

  tmp0.type() = ns.follow(tmp0.type());
  tmp1.type() = ns.follow(tmp1.type());

  if(tmp0.type().id()==ID_c_enum_tag)
    tmp0.type()=ns.follow_tag(to_c_enum_tag_type(tmp0.type()));

  if(tmp1.type().id()==ID_c_enum_tag)
    tmp1.type()=ns.follow_tag(to_c_enum_tag_type(tmp1.type()));

  const auto tmp0_const = expr_try_dynamic_cast<constant_exprt>(tmp0);
  const auto tmp1_const = expr_try_dynamic_cast<constant_exprt>(tmp1);

  // are _both_ constant?
  if(tmp0_const && tmp1_const)
  {
    if(expr.id() == ID_equal || expr.id() == ID_notequal)
    {

      bool equal = (tmp0_const->get_value() == tmp1_const->get_value());
      expr.make_bool(expr.id() == ID_equal ? equal : !equal);
      return false;
    }

    if(tmp0.type().id() == ID_fixedbv)
    {
      fixedbvt f0(to_constant_expr(tmp0));
      fixedbvt f1(to_constant_expr(tmp1));

      if(expr.id() == ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        UNREACHABLE;

      return false;
    }
    else if(tmp0.type().id()==ID_floatbv)
    {
      ieee_floatt f0(to_constant_expr(tmp0));
      ieee_floatt f1(to_constant_expr(tmp1));

      if(expr.id() == ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        UNREACHABLE;

      return false;
    }
    else if(tmp0.type().id()==ID_rational)
    {
      rationalt r0, r1;

      if(to_rational(tmp0, r0))
        return true;

      if(to_rational(tmp1, r1))
        return true;

      if(expr.id() == ID_ge)
        expr.make_bool(r0>=r1);
      else if(expr.id()==ID_le)
        expr.make_bool(r0<=r1);
      else if(expr.id()==ID_gt)
        expr.make_bool(r0>r1);
      else if(expr.id()==ID_lt)
        expr.make_bool(r0<r1);
      else
        UNREACHABLE;

      return false;
    }
    else
    {
      mp_integer v0, v1;

      if(to_integer(tmp0, v0))
        return true;

      if(to_integer(tmp1, v1))
        return true;

      if(expr.id() == ID_ge)
        expr.make_bool(v0>=v1);
      else if(expr.id()==ID_le)
        expr.make_bool(v0<=v1);
      else if(expr.id()==ID_gt)
        expr.make_bool(v0>v1);
      else if(expr.id()==ID_lt)
        expr.make_bool(v0<v1);
      else
        UNREACHABLE;

      return false;
    }
  }
  else if(tmp0_const)
  {
    // we want the constant on the RHS

    if(expr.id()==ID_ge)
      expr.id(ID_le);
    else if(expr.id()==ID_le)
      expr.id(ID_ge);
    else if(expr.id()==ID_gt)
      expr.id(ID_lt);
    else if(expr.id()==ID_lt)
      expr.id(ID_gt);

    expr.op0().swap(expr.op1());

    // one is constant
    simplify_inequality_constant(expr);
    return false;
  }
  else if(tmp1_const)
  {
    // one is constant
    return simplify_inequality_constant(expr);
  }
  else
  {
    // both are not constant
    return simplify_inequality_not_constant(expr);
  }
}

bool simplify_exprt::eliminate_common_addends(
  exprt &op0,
  exprt &op1)
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
    bool result=true;

    Forall_operands(it, op0)
      if(!eliminate_common_addends(*it, op1))
        result=false;

    return result;
  }
  else if(op1.id()==ID_plus)
  {
    bool result=true;

    Forall_operands(it, op1)
      if(!eliminate_common_addends(op0, *it))
        result=false;

    return result;
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

bool simplify_exprt::simplify_inequality_not_constant(exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  // pretty much all of the simplifications below are unsound
  // for IEEE float because of NaN!

  if(ns.follow(expr.op0().type()).id()==ID_floatbv)
    return true;

  // eliminate strict inequalities
  if(expr.id()==ID_notequal)
  {
    expr.id(ID_equal);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_gt)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_lt)
  {
    expr.id(ID_ge);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_node(expr);
    return false;
  }
  else if(expr.id()==ID_le)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    return false;
  }

  // now we only have >=, =

  INVARIANT(
    expr.id() == ID_ge || expr.id() == ID_equal,
    "we previously converted all other cases to >= or ==");

  // syntactically equal?

  if(operands.front()==operands.back())
  {
    expr=true_exprt();
    return false;
  }

  // try constants

  value_listt values0, values1;

  bool ok0=!get_values(expr.op0(), values0);
  bool ok1=!get_values(expr.op1(), values1);

  if(ok0 && ok1)
  {
    bool first=true;
    bool result=false; // dummy initialization to prevent warning
    bool ok=true;

    // compare possible values

    forall_value_list(it0, values0)
      forall_value_list(it1, values1)
      {
        bool tmp;
        const mp_integer &int_value0=*it0;
        const mp_integer &int_value1=*it1;

        if(expr.id()==ID_ge)
          tmp=(int_value0>=int_value1);
        else if(expr.id()==ID_equal)
          tmp=(int_value0==int_value1);
        else
        {
          tmp=false;
          UNREACHABLE;
        }

        if(first)
        {
          result=tmp;
          first=false;
        }
        else if(result!=tmp)
        {
          ok=false;
          break;
        }
      }

    if(ok)
    {
      expr.make_bool(result);
      return false;
    }
  }

  // See if we can eliminate common addends on both sides.
  // On bit-vectors, this is only sound on '='.
  if(expr.id()==ID_equal)
  {
    if(!eliminate_common_addends(expr.op0(), expr.op1()))
    {
      // remove zeros
      simplify_node(expr.op0());
      simplify_node(expr.op1());
      simplify_inequality(expr); // recursive call
      return false;
    }
  }

  return true;
}

/// \par parameters: an inequality with a constant on the RHS
bool simplify_exprt::simplify_inequality_constant(exprt &expr)
{
  // the constant is always on the RHS
  PRECONDITION(expr.op1().is_constant());

  if(expr.op0().id()==ID_if && expr.op0().operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    simplify_inequality_constant(if_expr.true_case());
    simplify_inequality_constant(if_expr.false_case());
    simplify_if(if_expr);
    expr.swap(if_expr);

    return false;
  }

  // do we deal with pointers?
  if(expr.op1().type().id()==ID_pointer)
  {
    if(expr.id()==ID_notequal)
    {
      expr.id(ID_equal);
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_node(expr);
      return false;
    }

    // very special case for pointers
    if(expr.id()==ID_equal &&
       expr.op1().is_constant() &&
       expr.op1().get(ID_value)==ID_NULL)
    {
      // the address of an object is never NULL

      if(expr.op0().id()==ID_address_of &&
         expr.op0().operands().size()==1)
      {
        if(expr.op0().op0().id()==ID_symbol ||
           expr.op0().op0().id()==ID_dynamic_object ||
           expr.op0().op0().id()==ID_member ||
           expr.op0().op0().id()==ID_index ||
           expr.op0().op0().id()==ID_string_constant)
        {
          expr=false_exprt();
          return false;
        }
      }
      else if(expr.op0().id()==ID_typecast &&
              expr.op0().operands().size()==1 &&
              expr.op0().type().id()==ID_pointer &&
              expr.op0().op0().id()==ID_address_of &&
              expr.op0().op0().operands().size()==1)
      {
        if(expr.op0().op0().op0().id()==ID_symbol ||
           expr.op0().op0().op0().id()==ID_dynamic_object ||
           expr.op0().op0().op0().id()==ID_member ||
           expr.op0().op0().op0().id()==ID_index ||
           expr.op0().op0().op0().id()==ID_string_constant)
        {
          expr=false_exprt();
          return false;
        }
      }
      else if(expr.op0().id()==ID_typecast &&
              expr.op0().operands().size()==1 &&
              expr.op0().type().id()==ID_pointer &&
              (expr.op0().op0().type().id()==ID_pointer ||
               config.ansi_c.NULL_is_zero))
      {
        // (type)ptr == NULL -> ptr == NULL
        // note that 'ptr' may be an integer
        exprt op=expr.op0().op0();
        expr.op0().swap(op);
        if(expr.op0().type().id()!=ID_pointer)
          expr.op1()=from_integer(0, expr.op0().type());
        else
          expr.op1().type()=expr.op0().type();
        simplify_inequality(expr); // do again!
        return false;
      }
    }

    // all we are doing with pointers
    return true;
  }

  // is it a separation predicate?

  if(expr.op0().id()==ID_plus)
  {
    // see if there is a constant in the sum

    if(expr.id()==ID_equal || expr.id()==ID_notequal)
    {
      mp_integer constant=0;
      bool changed=false;

      Forall_operands(it, expr.op0())
      {
        if(it->is_constant())
        {
          mp_integer i;
          if(!to_integer(*it, i))
          {
            constant+=i;
            *it=from_integer(0, it->type());
            CHECK_RETURN(it->is_not_nil());
            changed=true;
          }
        }
      }

      if(changed)
      {
        // adjust constant
        mp_integer i;
        to_integer(expr.op1(), i);
        i-=constant;
        expr.op1()=from_integer(i, expr.op1().type());

        simplify_plus(expr.op0());
        simplify_inequality(expr);
        return false;
      }
    }
  }

  #if 1
  // (double)value REL const ---> value rel const
  // if 'const' can be represented exactly.

  if(expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     ns.follow(expr.op0().type()).id()==ID_floatbv &&
     ns.follow(expr.op0().op0().type()).id()==ID_floatbv)
  {
    ieee_floatt const_val(to_constant_expr(expr.op1()));
    ieee_floatt const_val_converted=const_val;
    const_val_converted.change_spec(
      ieee_float_spect(to_floatbv_type(ns.follow(expr.op0().op0().type()))));
    ieee_floatt const_val_converted_back=const_val_converted;
    const_val_converted_back.change_spec(
      ieee_float_spect(to_floatbv_type(ns.follow(expr.op0().type()))));
    if(const_val_converted_back==const_val)
    {
      exprt result=expr;
      result.op0()=expr.op0().op0();
      result.op1()=const_val_converted.to_expr();
      expr.swap(result);
      return false;
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
      expr=true_exprt();
      return false;
    }

    exprt &operand=expr.op0();

    if(expr.id()==ID_equal)
    {
      // rules below do not hold for >=
      if(operand.id()==ID_unary_minus)
      {
        if(operand.operands().size()!=1)
          return true;
        exprt tmp;
        tmp.swap(operand.op0());
        operand.swap(tmp);
        return false;
      }
      else if(operand.id()==ID_plus)
      {
        // simplify a+-b=0 to a=b

        if(operand.operands().size()==2)
        {
          // if we have -b+a=0, make that a+(-b)=0

          if(operand.op0().id()==ID_unary_minus)
            operand.op0().swap(operand.op1());

          if(operand.op1().id()==ID_unary_minus &&
             operand.op1().operands().size()==1)
          {
            exprt tmp(expr.id(), expr.type());
            tmp.operands().resize(2);
            tmp.op0().swap(operand.op0());
            tmp.op1().swap(operand.op1().op0());
            expr.swap(tmp);
            return false;
          }
        }
      }
    }
  }

  // are we comparing with a typecast from bool?
  if(expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     expr.op0().op0().type().id()==ID_bool)
  {
    // we re-write (TYPE)boolean == 0 -> !boolean
    if(expr.op1().is_zero() && expr.id()==ID_equal)
    {
      expr=expr.op0().op0();
      expr.make_not();
      return false;
    }

    // we re-write (TYPE)boolean != 0 -> boolean
    if(expr.op1().is_zero() && expr.id()==ID_notequal)
    {
      expr=expr.op0().op0();
      return false;
    }
  }

  #define NORMALISE_CONSTANT_TESTS
  #ifdef NORMALISE_CONSTANT_TESTS
  // Normalise to >= and = to improve caching and term sharing
  if(expr.op0().type().id()==ID_unsignedbv ||
     expr.op0().type().id()==ID_signedbv)
  {
    bv_spect spec(expr.op0().type());
    mp_integer max(spec.max_value());

    if(expr.id()==ID_notequal)
    {
      expr.id(ID_equal);
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_node(expr);
      return false;
    }
    else if(expr.id()==ID_gt)
    {
      mp_integer i = numeric_cast_v<mp_integer>(expr.op1());

      if(i==max)
      {
        expr=false_exprt();
        return false;
      }

      expr.id(ID_ge);
      ++i;
      expr.op1()=from_integer(i, expr.op1().type());
      simplify_inequality_constant(expr);
      return false;
    }
    else if(expr.id()==ID_lt)
    {
      expr.id(ID_ge);
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_node(expr);
      return false;
    }
    else if(expr.id()==ID_le)
    {
      mp_integer i = numeric_cast_v<mp_integer>(expr.op1());

      if(i==max)
      {
        expr=true_exprt();
        return false;
      }

      expr.id(ID_ge);
      ++i;
      expr.op1()=from_integer(i, expr.op1().type());
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_node(expr);
      return false;
    }
  }
#endif
  return true;
}
