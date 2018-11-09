/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "replace_expr.h"
#include "std_expr.h"

bool simplify_exprt::simplify_index(exprt &expr)
{
  bool result=true;

  // extra arithmetic optimizations
  const exprt &index=to_index_expr(expr).index();
  const exprt &array=to_index_expr(expr).array();

  if(index.id()==ID_div &&
     index.operands().size()==2)
  {
    if(index.op0().id()==ID_mult &&
       index.op0().operands().size()==2 &&
       index.op0().op1()==index.op1())
    {
      exprt tmp=index.op0().op0();
      expr.op1()=tmp;
      result=false;
    }
    else if(index.op0().id()==ID_mult &&
            index.op0().operands().size()==2 &&
            index.op0().op0()==index.op1())
    {
      exprt tmp=index.op0().op1();
      expr.op1()=tmp;
      result=false;
    }
  }

  if(array.id()==ID_lambda)
  {
    // simplify (lambda i: e)(x) to e[i/x]

    const exprt &lambda_expr=array;

    if(lambda_expr.operands().size()!=2)
      return true;

    if(expr.op1().type()==lambda_expr.op0().type())
    {
      exprt tmp=lambda_expr.op1();
      replace_expr(lambda_expr.op0(), expr.op1(), tmp);
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_with)
  {
    // we have (a WITH [i:=e])[j]

    const exprt &with_expr=array;

    if(with_expr.operands().size()!=3)
      return true;

    if(with_expr.op1()==expr.op1())
    {
      // simplify (e with [i:=v])[i] to v
      exprt tmp=with_expr.op2();
      expr.swap(tmp);
      return false;
    }
    else
    {
      // Turn (a with i:=x)[j] into (i==j)?x:a[j].
      // watch out that the type of i and j might be different.
      equal_exprt equality_expr(expr.op1(), with_expr.op1());

      if(equality_expr.lhs().type()!=equality_expr.rhs().type())
        equality_expr.rhs().make_typecast(equality_expr.lhs().type());

      simplify_inequality(equality_expr);

      index_exprt new_index_expr;
      new_index_expr.type()=expr.type();
      new_index_expr.array()=with_expr.op0();
      new_index_expr.index()=expr.op1();

      simplify_index(new_index_expr); // recursive call

      if(equality_expr.is_true())
      {
        expr=with_expr.op2();
        return false;
      }
      else if(equality_expr.is_false())
      {
        expr.swap(new_index_expr);
        return false;
      }

      if_exprt if_expr(equality_expr, with_expr.op2(), new_index_expr);
      simplify_if(if_expr);

      expr.swap(if_expr);

      return false;
    }
  }
  else if(array.id()==ID_constant ||
          array.id()==ID_array)
  {
    const auto i = numeric_cast<mp_integer>(expr.op1());

    if(!i.has_value())
    {
    }
    else if(*i < 0 || *i >= array.operands().size())
    {
      // out of bounds
    }
    else
    {
      // ok
      exprt tmp = array.operands()[numeric_cast_v<std::size_t>(*i)];
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_string_constant)
  {
    const auto i = numeric_cast<mp_integer>(expr.op1());

    const irep_idt &value=array.get(ID_value);

    if(!i.has_value())
    {
    }
    else if(*i < 0 || *i > value.size())
    {
      // out of bounds
    }
    else
    {
      // terminating zero?
      const char v =
        (*i == value.size()) ? 0 : value[numeric_cast_v<std::size_t>(*i)];
      exprt tmp=from_integer(v, expr.type());
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_array_of)
  {
    if(array.operands().size()==1)
    {
      exprt tmp=array.op0();
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id() == ID_array_list)
  {
    // These are index/value pairs, alternating.
    for(size_t i=0; i<array.operands().size()/2; i++)
    {
      exprt tmp_index=array.operands()[i*2];
      tmp_index.make_typecast(index.type());
      simplify(tmp_index);
      if(tmp_index==index)
      {
        exprt tmp=array.operands()[i*2+1];
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(array.id()==ID_byte_extract_little_endian ||
          array.id()==ID_byte_extract_big_endian)
  {
    if(array.type().id() == ID_array)
    {
      const auto &array_type = to_array_type(array.type());

      // This rewrites byte_extract(s, o, array_type)[i]
      // to byte_extract(s, o+offset, sub_type)

      auto sub_size = pointer_offset_size(array_type.subtype(), ns);
      if(!sub_size.has_value())
        return true;

      // add offset to index
      mult_exprt offset(from_integer(*sub_size, array.op1().type()), index);
      plus_exprt final_offset(array.op1(), offset);
      simplify_node(final_offset);

      exprt result_expr(array.id(), expr.type());
      result_expr.add_to_operands(array.op0(), final_offset);
      expr.swap(result_expr);

      simplify_rec(expr);

      return false;
    }
  }
  else if(array.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(array);
    exprt cond=if_expr.cond();

    index_exprt idx_false=to_index_expr(expr);
    idx_false.array()=if_expr.false_case();

    to_index_expr(expr).array()=if_expr.true_case();

    expr=if_exprt(cond, expr, idx_false, expr.type());
    simplify_rec(expr);

    return false;
  }

  return result;
}
