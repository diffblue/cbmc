/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <util/arith_tools.h>

std::ostream &operator<<(std::ostream &out, const smt2_parsert::smt2_format &f)
{
  if(f.type.id() == ID_unsignedbv)
    out << "(_ BitVec " << to_unsignedbv_type(f.type).get_width() << ')';
  else if(f.type.id() == ID_bool)
    out << "Bool";
  else if(f.type.id() == ID_integer)
    out << "Int";
  else if(f.type.id() == ID_real)
    out << "Real";
  else
    out << "? " << f.type.id();

  return out;
}

void smt2_parsert::command_sequence()
{
  exit=false;

  while(next_token()==OPEN)
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol as command" << eom;
      return;
    }

    command(buffer);

    if(exit)
      return;

    switch(next_token())
    {
    case END_OF_FILE:
      error() << "expected closing parenthesis at end of command,"
                 " but got EOF" << eom;
      return;

    case CLOSE:
      // what we expect
      break;

    default:
      error() << "expected end of command" << eom;
      return;
    }
  }

  if(token!=END_OF_FILE)
  {
    error() << "unexpected token in command sequence" << eom;
  }
}

void smt2_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(peek())
    {
    case OPEN:
      next_token();
      parentheses++;
      break;

    case CLOSE:
      if(parentheses==0)
        return; // done

      next_token();
      parentheses--;
      break;

    case END_OF_FILE:
      error() << "unexpected EOF in command" << eom;
      return;

    default:
      next_token();
    }
  }
}
exprt::operandst smt2_parsert::operands()
{
  exprt::operandst result;

  while(peek()!=CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}

irep_idt smt2_parsert::get_fresh_id(const irep_idt &id)
{
  if(id_map[id].type.is_nil())
    return id; // id not yet used

  auto &count=renaming_counters[id];
  irep_idt new_id;
  do
  {
    new_id=id2string(id)+'#'+std::to_string(count);
    count++;
  }
  while(id_map.find(new_id)!=id_map.end());

  // record renaming
  renaming_map[id]=new_id;

  return new_id;
}

irep_idt smt2_parsert::rename_id(const irep_idt &id) const
{
  auto it=renaming_map.find(id);

  if(it==renaming_map.end())
    return id;
  else
    return it->second;
}

exprt smt2_parsert::let_expression()
{
  if(next_token()!=OPEN)
  {
    error() << "expected bindings after let" << eom;
    return nil_exprt();
  }

  std::vector<std::pair<irep_idt, exprt>> bindings;

  while(peek()==OPEN)
  {
    next_token();

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in binding" << eom;
      return nil_exprt();
    }

    irep_idt identifier=buffer;

    // note that the previous bindings are _not_ visible yet
    exprt value=expression();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' after value in binding" << eom;
      return nil_exprt();
    }

    bindings.push_back(
      std::pair<irep_idt, exprt>(identifier, value));
  }

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' at end of bindings" << eom;
    return nil_exprt();
  }

  // save the renaming map
  renaming_mapt old_renaming_map=renaming_map;

  // go forwards, add to id_map, renaming if need be
  for(auto &b : bindings)
  {
    // get a fresh id for it
    b.first=get_fresh_id(b.first);
    auto &entry=id_map[b.first];
    entry.type=b.second.type();
    entry.definition=b.second;
  }

  exprt expr=expression();

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' after let" << eom;
    return nil_exprt();
  }

  exprt result=expr;

  // go backwards, build let_expr
  for(auto r_it=bindings.rbegin(); r_it!=bindings.rend(); r_it++)
  {
    const let_exprt let(
      symbol_exprt(r_it->first, r_it->second.type()),
      r_it->second,
      result);
    result=let;
  }

  // remove bindings from id_map
  for(const auto &b : bindings)
    id_map.erase(b.first);

  // restore renamings
  renaming_map=old_renaming_map;

  return result;
}

exprt smt2_parsert::quantifier_expression(irep_idt id)
{
  if(next_token()!=OPEN)
  {
    error() << "expected bindings after " << id << eom;
    return nil_exprt();
  }

  std::vector<symbol_exprt> bindings;

  while(peek()==OPEN)
  {
    next_token();

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in binding" << eom;
      return nil_exprt();
    }

    irep_idt identifier=buffer;

    typet type=sort();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' after sort in binding" << eom;
      return nil_exprt();
    }

    bindings.push_back(symbol_exprt(identifier, type));
  }

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' at end of bindings" << eom;
    return nil_exprt();
  }

  // go forwards, add to id_map
  for(const auto &b : bindings)
  {
    auto &entry=id_map[b.get_identifier()];
    entry.type=b.type();
    entry.definition=nil_exprt();
  }

  exprt expr=expression();

  if(next_token()!=CLOSE)
  {
    error() << "expected ')' after " << id << eom;
    return nil_exprt();
  }

  exprt result=expr;

  // remove bindings from id_map
  for(const auto &b : bindings)
    id_map.erase(b.get_identifier());

  // go backwards, build quantified expression
  for(auto r_it=bindings.rbegin(); r_it!=bindings.rend(); r_it++)
  {
    binary_predicate_exprt quantifier(id);
    quantifier.op0()=*r_it;
    quantifier.op1().swap(result);
    result=quantifier;
  }

  return result;
}

exprt smt2_parsert::function_application(
  const irep_idt &,
  const exprt::operandst &)
{
  #if 0
  const auto &f = id_map[identifier];

  // check the arguments
  if(op.size()!=f.type.variables().size())
  {
    error() << "wrong number of arguments for function" << eom;
    return nil_exprt();
  }

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != f.type.variables()[i].type())
    {
      error() << "wrong type for arguments for function" << eom;
      return nil_exprt();
    }
  }

  return function_application_exprt(
    symbol_exprt(identifier, f.type), op, f.type.range());
  #endif
  return nil_exprt();
}

exprt::operandst smt2_parsert::cast_bv_to_signed(const exprt::operandst &op)
{
  exprt::operandst result = op;

  for(auto &expr : result)
  {
    if(expr.type().id() == ID_signedbv) // no need to cast
    {
    }
    else if(expr.type().id() != ID_unsignedbv)
    {
      error() << "expected unsigned bitvector" << eom;
    }
    else
    {
      const auto width = to_unsignedbv_type(expr.type()).get_width();
      expr = typecast_exprt(expr, signedbv_typet(width));
    }
  }

  return result;
}

exprt smt2_parsert::cast_bv_to_unsigned(const exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv) // no need to cast
    return expr;

  if(expr.type().id()!=ID_signedbv)
  {
    error() << "expected signed bitvector" << eom;
    return expr;
  }

  const auto width=to_signedbv_type(expr.type()).get_width();
  return typecast_exprt(expr, unsignedbv_typet(width));
}

exprt smt2_parsert::multi_ary(irep_idt id, const exprt::operandst &op)
{
  if(op.empty())
  {
    error() << "expression must have at least one operand" << eom;
    return nil_exprt();
  }
  else
  {
    for(std::size_t i=1; i<op.size(); i++)
    {
      if(op[i].type()!=op[0].type())
      {
        error() << "expression must have operands with matching types,"
                   " but got `"
                << smt2_format(op[0].type()) << "' and `"
                << smt2_format(op[i].type()) << '\'' << eom;
        return nil_exprt();
      }
    }

    exprt result(id, op[0].type());
    result.operands() = op;
    return result;
  }
}

exprt smt2_parsert::binary_predicate(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=2)
  {
    error() << "expression must have two operands" << eom;
    return nil_exprt();
  }
  else
  {
    if(op[0].type()!=op[1].type())
    {
      error() << "expression must have operands with matching types,"
                 " but got `"
              << smt2_format(op[0].type()) << "' and `"
              << smt2_format(op[1].type()) << '\'' << eom;
      return nil_exprt();
    }

    return binary_predicate_exprt(op[0], id, op[1]);
  }
}

exprt smt2_parsert::unary(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=1)
  {
    error() << "expression must have one operand" << eom;
    return nil_exprt();
  }
  else
    return unary_exprt(id, op[0], op[0].type());
}

exprt smt2_parsert::binary(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=2)
  {
    error() << "expression must have two operands" << eom;
    return nil_exprt();
  }
  else
  {
    if(op[0].type()!=op[1].type())
    {
      error() << "expression must have operands with matching types" << eom;
      return nil_exprt();
    }

    return binary_exprt(op[0], id, op[1], op[0].type());
  }
}

exprt smt2_parsert::function_application()
{
  switch(next_token())
  {
  case SYMBOL:
    if(buffer=="_") // indexed identifier
    {
      // indexed identifier
      if(next_token()!=SYMBOL)
      {
        error() << "expected symbol after '_'" << eom;
        return nil_exprt();
      }

      if(has_prefix(buffer, "bv"))
      {
        mp_integer i=string2integer(std::string(buffer, 2, std::string::npos));

        if(next_token()!=NUMERAL)
        {
          error() << "expected numeral as bitvector literal width" << eom;
          return nil_exprt();
        }

        auto width=std::stoll(buffer);

        if(next_token()!=CLOSE)
        {
          error() << "expected ')' after bitvector literal" << eom;
          return nil_exprt();
        }

        return from_integer(i, unsignedbv_typet(width));
      }
      else
      {
        error() << "unknown indexed identifier " << buffer << eom;
        return nil_exprt();
      }
    }
    else
    {
      // non-indexed symbol; hash it
      const irep_idt id=buffer;

      if(id==ID_let)
        return let_expression();
      else if(id==ID_forall || id==ID_exists)
        return quantifier_expression(id);

      auto op=operands();

      if(id==ID_and ||
         id==ID_or ||
         id==ID_xor)
      {
        return multi_ary(id, op);
      }
      else if(id==ID_not)
      {
        return unary(id, op);
      }
      else if(id==ID_equal ||
              id==ID_le ||
              id==ID_ge ||
              id==ID_lt ||
              id==ID_gt)
      {
        return binary_predicate(id, op);
      }
      else if(id=="bvule")
      {
        return binary_predicate(ID_le, op);
      }
      else if(id=="bvsle")
      {
        return binary_predicate(ID_le, cast_bv_to_signed(op));
      }
      else if(id=="bvuge")
      {
        return binary_predicate(ID_ge, op);
      }
      else if(id=="bvsge")
      {
        return binary_predicate(ID_ge, cast_bv_to_signed(op));
      }
      else if(id=="bvult")
      {
        return binary_predicate(ID_lt, op);
      }
      else if(id=="bvslt")
      {
        return binary_predicate(ID_lt, cast_bv_to_signed(op));
      }
      else if(id=="bvugt")
      {
        return binary_predicate(ID_gt, op);
      }
      else if(id=="bvsgt")
      {
        return binary_predicate(ID_gt, cast_bv_to_signed(op));
      }
      else if(id=="bvashr")
      {
        return cast_bv_to_unsigned(binary(ID_ashr, cast_bv_to_signed(op)));
      }
      else if(id=="bvlshr" || id=="bvshr")
      {
        return binary(ID_lshr, op);
      }
      else if(id=="bvlshr" || id=="bvashl" || id=="bvshl")
      {
        return binary(ID_shl, op);
      }
      else if(id=="bvand")
      {
        return multi_ary(ID_bitand, op);
      }
      else if(id=="bvnand")
      {
        return multi_ary(ID_bitnand, op);
      }
      else if(id=="bvor")
      {
        return multi_ary(ID_bitor, op);
      }
      else if(id=="bvnor")
      {
        return multi_ary(ID_bitnor, op);
      }
      else if(id=="bvxor")
      {
        return multi_ary(ID_bitxor, op);
      }
      else if(id=="bvxnor")
      {
        return multi_ary(ID_bitxnor, op);
      }
      else if(id=="bvnot")
      {
        return unary(ID_bitnot, op);
      }
      else if(id=="bvneg")
      {
        return unary(ID_unary_minus, op);
      }
      else if(id=="bvadd")
      {
        return multi_ary(ID_plus, op);
      }
      else if(id==ID_plus)
      {
        return multi_ary(id, op);
      }
      else if(id=="bvsub" || id=="-")
      {
        return binary(ID_minus, op);
      }
      else if(id=="bvmul" || id=="*")
      {
        return binary(ID_mult, op);
      }
      else if(id=="bvsdiv")
      {
        return cast_bv_to_unsigned(binary(ID_div, cast_bv_to_signed(op)));
      }
      else if(id=="bvudiv")
      {
        return binary(ID_div, op);
      }
      else if(id=="/" || id=="div")
      {
        return binary(ID_div, op);
      }
      else if(id=="bvsrem")
      {
        // 2's complement signed remainder (sign follows dividend)
        // This matches our ID_mod, and what C does since C99.
        return cast_bv_to_unsigned(binary(ID_mod, cast_bv_to_signed(op)));
      }
      else if(id=="bvsmod")
      {
        // 2's complement signed remainder (sign follows divisor)
        // We don't have that.
        return cast_bv_to_unsigned(binary(ID_mod, cast_bv_to_signed(op)));
      }
      else if(id=="bvurem" || id=="%")
      {
        return binary(ID_mod, op);
      }
      else if(id=="concat")
      {
        if(op.size()!=2)
        {
          error() << "concat takes two operands " << op.size() << eom;
          return nil_exprt();
        }

        auto width0=to_unsignedbv_type(op[0].type()).get_width();
        auto width1=to_unsignedbv_type(op[1].type()).get_width();

        unsignedbv_typet t(width0+width1);

        return binary_exprt(op[0], ID_concatenation, op[1], t);
      }
      else if(id=="distinct")
      {
        // pair-wise different constraint, multi-ary
        return multi_ary("distinct", op);
      }
      else if(id=="ite")
      {
        if(op.size()!=3)
        {
          error() << "ite takes three operands" << eom;
          return nil_exprt();
        }

        if(op[0].type().id()!=ID_bool)
        {
          error() << "ite takes a boolean as first operand" << eom;
          return nil_exprt();
        }

        if(op[1].type()!=op[2].type())
        {
          error() << "ite needs matching types" << eom;
          return nil_exprt();
        }

        return if_exprt(op[0], op[1], op[2]);
      }
      else if(id=="=>" || id=="implies")
      {
        return binary(ID_implies, op);
      }
      else
      {
        // rummage through id_map
        const irep_idt final_id=rename_id(id);
        auto id_it=id_map.find(final_id);
        if(id_it!=id_map.end())
        {
          if(id_it->second.type.id()==ID_mathematical_function)
          {
            return function_application_exprt(
              symbol_exprt(final_id, id_it->second.type),
              op,
              to_mathematical_function_type(
                id_it->second.type).codomain());
          }
          else
            return symbol_exprt(final_id, id_it->second.type);
        }

        error() << "2 unknown symbol " << id << eom;
        return nil_exprt();
      }
    }
    break;

  case OPEN: // likely indexed identifier
    if(peek()==SYMBOL)
    {
      next_token(); // eat symbol
      if(buffer=="_")
      {
        // indexed identifier
        if(next_token()!=SYMBOL)
        {
          error() << "expected symbol after '_'" << eom;
          return nil_exprt();
        }

        irep_idt id=buffer; // hash it

        if(id=="extract")
        {
          if(next_token()!=NUMERAL)
          {
            error() << "expected numeral after extract" << eom;
            return nil_exprt();
          }

          auto upper=std::stoll(buffer);

          if(next_token()!=NUMERAL)
          {
            error() << "expected two numerals after extract" << eom;
            return nil_exprt();
          }

          auto lower=std::stoll(buffer);

          if(next_token()!=CLOSE)
          {
            error() << "expected ')' after extract" << eom;
            return nil_exprt();
          }

          auto op=operands();

          if(op.size()!=1)
          {
            error() << "extract takes one operand" << eom;
            return nil_exprt();
          }

          auto upper_e=from_integer(upper, integer_typet());
          auto lower_e=from_integer(lower, integer_typet());

          if(upper<lower)
          {
            error() << "extract got bad indices" << eom;
            return nil_exprt();
          }

          unsignedbv_typet t(upper-lower+1);

          return extractbits_exprt(op[0], upper_e, lower_e, t);
        }
        else if(id=="rotate_left" ||
                id=="rotate_right" ||
                id == ID_repeat ||
                id=="sign_extend" ||
                id=="zero_extend")
        {
          if(next_token()!=NUMERAL)
          {
            error() << "expected numeral after " << id << eom;
            return nil_exprt();
          }

          auto index=std::stoll(buffer);

          if(next_token()!=CLOSE)
          {
            error() << "expected ')' after " << id << " index" << eom;
            return nil_exprt();
          }

          auto op=operands();

          if(op.size()!=1)
          {
            error() << id << " takes one operand" << eom;
            return nil_exprt();
          }

          if(id=="rotate_left")
          {
            auto dist=from_integer(index, integer_typet());
            return binary_exprt(op[0], ID_rol, dist, op[0].type());
          }
          else if(id=="rotate_right")
          {
            auto dist=from_integer(index, integer_typet());
            return binary_exprt(op[0], ID_ror, dist, op[0].type());
          }
          else if(id=="sign_extend")
          {
            auto width=to_unsignedbv_type(op[0].type()).get_width();
            signedbv_typet signed_type(width+index);
            unsignedbv_typet unsigned_type(width+index);

            return typecast_exprt(
              typecast_exprt(op[0], signed_type), unsigned_type);
          }
          else if(id=="zero_extend")
          {
            auto width=to_unsignedbv_type(op[0].type()).get_width();
            unsignedbv_typet unsigned_type(width+index);

            return typecast_exprt(op[0], unsigned_type);
          }
          else if(id == ID_repeat)
          {
            return nil_exprt();
          }
          else
            return nil_exprt();
        }
        else
        {
          error() << "unknown indexed identifier " << buffer << eom;
          return nil_exprt();
        }
      }
      else
      {
        // just double parentheses
        error() << "expected symbol or indexed identifier "
                   "after '(' in an expression" << eom;

        exprt tmp=expression();

        if(next_token()!=CLOSE && next_token()!=CLOSE)
          error() << "mismatched parentheses in an expression" << eom;

        return tmp;
      }
    }
    else
    {
      // just double parentheses
      error() << "expected symbol or indexed identifier "
                 "after '(' in an expression" << eom;

      exprt tmp=expression();

      if(next_token()!=CLOSE && next_token()!=CLOSE)
        error() << "mismatched parentheses in an expression" << eom;

      return tmp;
    }
    break;

  default:
    // just parentheses
    error() << "expected symbol or indexed identifier "
               "after '(' in an expression" << eom;

    exprt tmp=expression();
    if(next_token()!=CLOSE)
      error() << "mismatched parentheses in an expression" << eom;

    return tmp;
  }
}

exprt smt2_parsert::expression()
{
  switch(next_token())
  {
  case SYMBOL:
    {
      // hash it
      const irep_idt identifier=buffer;

      if(identifier==ID_true)
        return true_exprt();
      else if(identifier==ID_false)
        return false_exprt();
      else
      {
        // rummage through id_map
        const irep_idt final_id=rename_id(identifier);
        auto id_it=id_map.find(final_id);
        if(id_it!=id_map.end())
          return symbol_exprt(final_id, id_it->second.type);

        error() << "1 unknown symbol " << identifier << eom;
        return nil_exprt();
      }
    }

  case NUMERAL:
    if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='x')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 16);
      const std::size_t width = 4*(buffer.size() - 2);
      CHECK_RETURN(width!=0 && width%4==0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else if(buffer.size()>=2 && buffer[0]=='#' && buffer[1]=='b')
    {
      mp_integer value=
        string2integer(std::string(buffer, 2, std::string::npos), 2);
      const std::size_t width = buffer.size() - 2;
      CHECK_RETURN(width!=0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else
    {
      return constant_exprt(buffer, integer_typet());
    }

  case OPEN: // function application
    return function_application();

  case END_OF_FILE:
    error() << "EOF in an expression" << eom;
    return nil_exprt();

  default:
    error() << "unexpected token in an expression" << eom;
    return nil_exprt();
  }
}

typet smt2_parsert::sort()
{
  switch(next_token())
  {
  case SYMBOL:
    if(buffer=="Bool")
      return bool_typet();
    else if(buffer=="Int")
      return integer_typet();
    else if(buffer=="Real")
      return real_typet();
    else
    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  case OPEN:
    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol after '(' in a sort " << eom;
      return nil_typet();
    }

    if(buffer=="_")
    {
      // indexed identifier
      if(next_token()!=SYMBOL)
      {
        error() << "expected symbol after '_' in a sort" << eom;
        return nil_typet();
      }

      if(buffer=="BitVec")
      {
        if(next_token()!=NUMERAL)
        {
          error() << "expected numeral as bit-width" << eom;
          return nil_typet();
        }

        auto width=std::stoll(buffer);

        // eat the ')'
        if(next_token()!=CLOSE)
        {
          error() << "expected ')' at end of sort" << eom;
          return nil_typet();
        }

        return unsignedbv_typet(width);
      }
      else
      {
        error() << "unexpected sort: `" << buffer << '\'' << eom;
        return nil_typet();
      }
    }
    else if(buffer == "Array")
    {
      // this gets two sorts as arguments, domain and range
      auto domain = sort();
      auto range = sort();

      // eat the ')'
      if(next_token() != CLOSE)
      {
        error() << "expected ')' at end of Array sort" << eom;
        return nil_typet();
      }

      // we can turn arrays that map an unsigned bitvector type
      // to something else into our 'array_typet'
      if(domain.id() == ID_unsignedbv)
      {
        const auto size = to_unsignedbv_type(domain).largest_expr();
        return array_typet(range, size);
      }
      else
      {
        error() << "unsupported array sort" << eom;
        return nil_typet();
      }
    }
    else
    {
      error() << "unexpected sort: `" << buffer << '\'' << eom;
      return nil_typet();
    }

  default:
    error() << "unexpected token in a sort " << buffer << eom;
    return nil_typet();
  }
}

typet smt2_parsert::function_signature_definition()
{
  if(next_token()!=OPEN)
  {
    error() << "expected '(' at beginning of signature" << eom;
    return nil_typet();
  }

  if(peek()==CLOSE)
  {
    next_token(); // eat the ')'
    return sort();
  }

  mathematical_function_typet::domaint domain;

  while(peek()!=CLOSE)
  {
    if(next_token()!=OPEN)
    {
      error() << "expected '(' at beginning of parameter" << eom;
      return nil_typet();
    }

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in parameter" << eom;
      return nil_typet();
    }

    mathematical_function_typet::variablet var;
    std::string id=buffer;
    var.set_identifier(id);
    var.type()=sort();
    domain.push_back(var);

    auto &entry=id_map[id];
    entry.type=var.type();
    entry.definition=nil_exprt();

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' at end of parameter" << eom;
      return nil_typet();
    }
  }

  next_token(); // eat the ')'

  typet codomain = sort();

  return mathematical_function_typet(domain, codomain);
}

typet smt2_parsert::function_signature_declaration()
{
  if(next_token()!=OPEN)
  {
    error() << "expected '(' at beginning of signature" << eom;
    return nil_typet();
  }

  if(peek()==CLOSE)
  {
    next_token(); // eat the ')'
    return sort();
  }

  mathematical_function_typet::domaint domain;

  while(peek()!=CLOSE)
  {
    if(next_token()!=OPEN)
    {
      error() << "expected '(' at beginning of parameter" << eom;
      return nil_typet();
    }

    if(next_token()!=SYMBOL)
    {
      error() << "expected symbol in parameter" << eom;
      return nil_typet();
    }

    mathematical_function_typet::variablet var;
    var.type()=sort();
    domain.push_back(var);

    if(next_token()!=CLOSE)
    {
      error() << "expected ')' at end of parameter" << eom;
      return nil_typet();
    }
  }

  next_token(); // eat the ')'

  typet codomain = sort();

  return mathematical_function_typet(domain, codomain);
}

void smt2_parsert::command(const std::string &c)
{
  if(c == "declare-const" || c == "declare-var")
  {
    // declare-var appears to be a synonym for declare-const that is
    // accepted by Z3 and CVC4
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after " << c << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(id_map.find(id)!=id_map.end())
    {
      error() << "identifier `" << id << "' defined twice" << eom;
      ignore_command();
      return;
    }

    auto &entry = id_map[id];
    entry.type = sort();
    entry.definition = nil_exprt();
  }
  else if(c=="declare-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after declare-fun" << eom;
      ignore_command();
      return;
    }

    irep_idt id=buffer;

    if(id_map.find(id)!=id_map.end())
    {
      error() << "identifier `" << id << "' defined twice" << eom;
      ignore_command();
      return;
    }

    auto &entry=id_map[id];
    entry.type=function_signature_declaration();
    entry.definition=nil_exprt();
  }
  else if(c=="define-fun")
  {
    if(next_token()!=SYMBOL)
    {
      error() << "expected a symbol after define-fun" << eom;
      ignore_command();
      return;
    }

    const irep_idt id=buffer;

    if(id_map.find(id)!=id_map.end())
    {
      error() << "identifier `" << id << "' defined twice" << eom;
      ignore_command();
      return;
    }

    // create the entry
    id_map[id];

    auto signature=function_signature_definition();
    exprt body=expression();

    // check type of body
    if(signature.id() == ID_mathematical_function)
    {
      const auto &f_signature = to_mathematical_function_type(signature);
      if(body.type() != f_signature.codomain())
      {
        error() << "type mismatch in function definition: expected `"
                << smt2_format(f_signature.codomain()) << "' but got `"
                << smt2_format(body.type()) << '\'' << eom;
        return;
      }
    }
    else if(body.type() != signature)
    {
      error() << "type mismatch in function definition: expected `"
              << smt2_format(signature) << "' but got `"
              << smt2_format(body.type()) << '\'' << eom;
      return;
    }

    // set up the entry
    auto &entry=id_map[id];
    entry.type=signature;
    entry.definition=body;
  }
  else if(c=="exit")
  {
    exit=true;
  }
  else
    ignore_command();
}
