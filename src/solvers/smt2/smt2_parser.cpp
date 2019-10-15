/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include "smt2_format.h"

#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/prefix.h>
#include <util/range.h>

#include <numeric>

smt2_tokenizert::tokent smt2_parsert::next_token()
{
  const auto token = smt2_tokenizer.next_token();

  if(token == smt2_tokenizert::OPEN)
    parenthesis_level++;
  else if(token == smt2_tokenizert::CLOSE)
    parenthesis_level--;

  return token;
}

void smt2_parsert::skip_to_end_of_list()
{
  while(parenthesis_level > 0)
    if(next_token() == smt2_tokenizert::END_OF_FILE)
      return;
}

void smt2_parsert::command_sequence()
{
  exit=false;

  while(!exit)
  {
    if(smt2_tokenizer.peek() == smt2_tokenizert::END_OF_FILE)
    {
      exit = true;
      return;
    }

    if(next_token() != smt2_tokenizert::OPEN)
      throw error("command must start with '('");

    if(next_token() != smt2_tokenizert::SYMBOL)
    {
      ignore_command();
      throw error("expected symbol as command");
    }

    command(smt2_tokenizer.get_buffer());

    switch(next_token())
    {
    case smt2_tokenizert::END_OF_FILE:
      throw error(
        "expected closing parenthesis at end of command,"
        " but got EOF");

    case smt2_tokenizert::CLOSE:
      // what we expect
      break;

    case smt2_tokenizert::OPEN:
    case smt2_tokenizert::SYMBOL:
    case smt2_tokenizert::NUMERAL:
    case smt2_tokenizert::STRING_LITERAL:
    case smt2_tokenizert::NONE:
    case smt2_tokenizert::KEYWORD:
      throw error("expected ')' at end of command");
    }
  }
}

void smt2_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(smt2_tokenizer.peek())
    {
    case smt2_tokenizert::OPEN:
      next_token();
      parentheses++;
      break;

    case smt2_tokenizert::CLOSE:
      if(parentheses==0)
        return; // done

      next_token();
      parentheses--;
      break;

    case smt2_tokenizert::END_OF_FILE:
      throw error("unexpected EOF in command");

    case smt2_tokenizert::SYMBOL:
    case smt2_tokenizert::NUMERAL:
    case smt2_tokenizert::STRING_LITERAL:
    case smt2_tokenizert::NONE:
    case smt2_tokenizert::KEYWORD:
      next_token();
    }
  }
}

exprt::operandst smt2_parsert::operands()
{
  exprt::operandst result;

  while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
    result.push_back(expression());

  next_token(); // eat the ')'

  return result;
}

irep_idt smt2_parsert::add_fresh_id(
  const irep_idt &id,
  idt::kindt kind,
  const exprt &expr)
{
  auto &count=renaming_counters[id];
  irep_idt new_id;
  do
  {
    new_id=id2string(id)+'#'+std::to_string(count);
    count++;
  } while(!id_map
             .emplace(
               std::piecewise_construct,
               std::forward_as_tuple(new_id),
               std::forward_as_tuple(kind, expr))
             .second);

  // record renaming
  renaming_map[id] = new_id;

  return new_id;
}

void smt2_parsert::add_unique_id(const irep_idt &id, const exprt &expr)
{
  if(!id_map
        .emplace(
          std::piecewise_construct,
          std::forward_as_tuple(id),
          std::forward_as_tuple(idt::VARIABLE, expr))
        .second)
  {
    // id already used
    throw error() << "identifier '" << id << "' defined twice";
  }
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
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected bindings after let");

  std::vector<std::pair<irep_idt, exprt>> bindings;

  while(smt2_tokenizer.peek() == smt2_tokenizert::OPEN)
  {
    next_token();

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in binding");

    irep_idt identifier = smt2_tokenizer.get_buffer();

    // note that the previous bindings are _not_ visible yet
    exprt value=expression();

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' after value in binding");

    bindings.push_back(
      std::pair<irep_idt, exprt>(identifier, value));
  }

  if(next_token() != smt2_tokenizert::CLOSE)
    throw error("expected ')' at end of bindings");

  // save the renaming map
  renaming_mapt old_renaming_map=renaming_map;

  // go forwards, add to id_map, renaming if need be
  for(auto &b : bindings)
  {
    // get a fresh id for it
    b.first = add_fresh_id(b.first, idt::BINDING, b.second);
  }

  exprt where = expression();

  if(next_token() != smt2_tokenizert::CLOSE)
    throw error("expected ')' after let");

  binding_exprt::variablest variables;
  exprt::operandst values;

  for(const auto &b : bindings)
  {
    variables.push_back(symbol_exprt(b.first, b.second.type()));
    values.push_back(b.second);
  }

  // we keep these in the id_map in order to retain globally
  // unique identifiers

  // restore renamings
  renaming_map=old_renaming_map;

  return let_exprt(variables, values, where);
}

exprt smt2_parsert::quantifier_expression(irep_idt id)
{
  if(next_token() != smt2_tokenizert::OPEN)
    throw error() << "expected bindings after " << id;

  std::vector<symbol_exprt> bindings;

  while(smt2_tokenizer.peek() == smt2_tokenizert::OPEN)
  {
    next_token();

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in binding");

    irep_idt identifier = smt2_tokenizer.get_buffer();

    typet type=sort();

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' after sort in binding");

    bindings.push_back(symbol_exprt(identifier, type));
  }

  if(next_token() != smt2_tokenizert::CLOSE)
    throw error("expected ')' at end of bindings");

  // save the renaming map
  renaming_mapt old_renaming_map = renaming_map;

  // go forwards, add to id_map, renaming if need be
  for(auto &b : bindings)
  {
    const irep_idt id =
      add_fresh_id(b.get_identifier(), idt::BINDING, exprt(ID_nil, b.type()));

    b.set_identifier(id);
  }

  exprt expr=expression();

  if(next_token() != smt2_tokenizert::CLOSE)
    throw error() << "expected ')' after " << id;

  exprt result=expr;

  // remove bindings from id_map
  for(const auto &b : bindings)
    id_map.erase(b.get_identifier());

  // restore renaming map
  renaming_map = old_renaming_map;

  // go backwards, build quantified expression
  for(auto r_it=bindings.rbegin(); r_it!=bindings.rend(); r_it++)
  {
    quantifier_exprt quantifier(id, *r_it, result);
    result=quantifier;
  }

  return result;
}

exprt smt2_parsert::function_application(
  const symbol_exprt &function,
  const exprt::operandst &op)
{
  const auto &function_type = to_mathematical_function_type(function.type());

  // check the arguments
  if(op.size() != function_type.domain().size())
    throw error("wrong number of arguments for function");

  for(std::size_t i=0; i<op.size(); i++)
  {
    if(op[i].type() != function_type.domain()[i])
      throw error("wrong type for arguments for function");
  }

  return function_application_exprt(function, op);
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
      throw error("expected unsigned bitvector");
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
    throw error("expected signed bitvector");

  const auto width=to_signedbv_type(expr.type()).get_width();
  return typecast_exprt(expr, unsignedbv_typet(width));
}

exprt smt2_parsert::multi_ary(irep_idt id, const exprt::operandst &op)
{
  if(op.empty())
    throw error("expression must have at least one operand");

  for(std::size_t i = 1; i < op.size(); i++)
  {
    if(op[i].type() != op[0].type())
    {
      throw error() << "expression must have operands with matching types,"
                       " but got '"
                    << smt2_format(op[0].type()) << "' and '"
                    << smt2_format(op[i].type()) << '\'';
    }
  }

  exprt result(id, op[0].type());
  result.operands() = op;
  return result;
}

exprt smt2_parsert::binary_predicate(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=2)
    throw error("expression must have two operands");

  if(op[0].type() != op[1].type())
  {
    throw error() << "expression must have operands with matching types,"
                     " but got '"
                  << smt2_format(op[0].type()) << "' and '"
                  << smt2_format(op[1].type()) << '\'';
  }

  return binary_predicate_exprt(op[0], id, op[1]);
}

exprt smt2_parsert::unary(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=1)
    throw error("expression must have one operand");

  return unary_exprt(id, op[0], op[0].type());
}

exprt smt2_parsert::binary(irep_idt id, const exprt::operandst &op)
{
  if(op.size()!=2)
    throw error("expression must have two operands");

  if(op[0].type() != op[1].type())
    throw error("expression must have operands with matching types");

  return binary_exprt(op[0], id, op[1], op[0].type());
}

exprt smt2_parsert::function_application_ieee_float_eq(
  const exprt::operandst &op)
{
  if(op.size() != 2)
    throw error() << "FloatingPoint equality takes two operands";

  if(op[0].type().id() != ID_floatbv || op[1].type().id() != ID_floatbv)
    throw error() << "FloatingPoint equality takes FloatingPoint operands";

  if(op[0].type() != op[1].type())
  {
    throw error() << "FloatingPoint equality takes FloatingPoint operands with "
                  << "matching sort, but got " << smt2_format(op[0].type())
                  << " vs " << smt2_format(op[1].type());
  }

  return ieee_float_equal_exprt(op[0], op[1]);
}

exprt smt2_parsert::function_application_ieee_float_op(
  const irep_idt &id,
  const exprt::operandst &op)
{
  if(op.size() != 3)
    throw error() << id << " takes three operands";

  if(op[1].type().id() != ID_floatbv || op[2].type().id() != ID_floatbv)
    throw error() << id << " takes FloatingPoint operands";

  if(op[1].type() != op[2].type())
  {
    throw error() << id << " takes FloatingPoint operands with matching sort, "
                  << "but got " << smt2_format(op[1].type()) << " vs "
                  << smt2_format(op[2].type());
  }

  // clang-format off
  const irep_idt expr_id =
    id == "fp.add" ? ID_floatbv_plus :
    id == "fp.sub" ? ID_floatbv_minus :
    id == "fp.mul" ? ID_floatbv_mult :
    id == "fp.div" ? ID_floatbv_div :
    throw error("unsupported floating-point operation");
  // clang-format on

  return ieee_float_op_exprt(op[1], expr_id, op[2], op[0]);
}

exprt smt2_parsert::function_application_fp(const exprt::operandst &op)
{
  // floating-point from bit-vectors
  if(op.size() != 3)
    throw error("fp takes three operands");

  if(op[0].type().id() != ID_unsignedbv)
    throw error("fp takes BitVec as first operand");

  if(op[1].type().id() != ID_unsignedbv)
    throw error("fp takes BitVec as second operand");

  if(op[2].type().id() != ID_unsignedbv)
    throw error("fp takes BitVec as third operand");

  if(to_unsignedbv_type(op[0].type()).get_width() != 1)
    throw error("fp takes BitVec of size 1 as first operand");

  const auto width_e = to_unsignedbv_type(op[1].type()).get_width();
  const auto width_f = to_unsignedbv_type(op[2].type()).get_width();

  // stitch the bits together
  return typecast_exprt(
    concatenation_exprt(exprt::operandst(op), bv_typet(width_f + width_e + 1)),
    ieee_float_spect(width_f, width_e).to_type());
}

exprt smt2_parsert::function_application()
{
  switch(next_token())
  {
  case smt2_tokenizert::SYMBOL:
    if(smt2_tokenizer.get_buffer() == "_") // indexed identifier
    {
      // indexed identifier
      if(next_token() != smt2_tokenizert::SYMBOL)
        throw error("expected symbol after '_'");

      if(has_prefix(smt2_tokenizer.get_buffer(), "bv"))
      {
        mp_integer i = string2integer(
          std::string(smt2_tokenizer.get_buffer(), 2, std::string::npos));

        if(next_token() != smt2_tokenizert::NUMERAL)
          throw error("expected numeral as bitvector literal width");

        auto width = std::stoll(smt2_tokenizer.get_buffer());

        if(next_token() != smt2_tokenizert::CLOSE)
          throw error("expected ')' after bitvector literal");

        return from_integer(i, unsignedbv_typet(width));
      }
      else
      {
        throw error() << "unknown indexed identifier "
                      << smt2_tokenizer.get_buffer();
      }
    }
    else if(smt2_tokenizer.get_buffer() == "!")
    {
      // these are "term attributes"
      const auto term = expression();

      while(smt2_tokenizer.peek() == smt2_tokenizert::KEYWORD)
      {
        next_token(); // eat the keyword
        if(smt2_tokenizer.get_buffer() == "named")
        {
          // 'named terms' must be Boolean
          if(term.type().id() != ID_bool)
            throw error("named terms must be Boolean");

          if(next_token() == smt2_tokenizert::SYMBOL)
          {
            const symbol_exprt symbol_expr(
              smt2_tokenizer.get_buffer(), bool_typet());
            named_terms.emplace(
              symbol_expr.get_identifier(), named_termt(term, symbol_expr));
          }
          else
            throw error("invalid name attribute, expected symbol");
        }
        else
          throw error("unknown term attribute");
      }

      if(next_token() != smt2_tokenizert::CLOSE)
        throw error("expected ')' at end of term attribute");
      else
        return term;
    }
    else
    {
      // non-indexed symbol, look up in expression table
      const auto id = smt2_tokenizer.get_buffer();
      const auto e_it = expressions.find(id);
      if(e_it != expressions.end())
        return e_it->second();

      // get the operands
      auto op = operands();

      // rummage through id_map
      const irep_idt final_id = rename_id(id);
      auto id_it = id_map.find(final_id);
      if(id_it != id_map.end())
      {
        if(id_it->second.type.id() == ID_mathematical_function)
        {
          return function_application(
            symbol_exprt(final_id, id_it->second.type), op);
        }
        else
          return symbol_exprt(final_id, id_it->second.type);
      }

      throw error() << "unknown function symbol '" << id << '\'';
    }
    break;

  case smt2_tokenizert::OPEN: // likely indexed identifier
    if(smt2_tokenizer.peek() == smt2_tokenizert::SYMBOL)
    {
      next_token(); // eat symbol
      if(smt2_tokenizer.get_buffer() == "_")
      {
        // indexed identifier
        if(next_token() != smt2_tokenizert::SYMBOL)
          throw error("expected symbol after '_'");

        irep_idt id = smt2_tokenizer.get_buffer(); // hash it

        if(id=="extract")
        {
          if(next_token() != smt2_tokenizert::NUMERAL)
            throw error("expected numeral after extract");

          auto upper = std::stoll(smt2_tokenizer.get_buffer());

          if(next_token() != smt2_tokenizert::NUMERAL)
            throw error("expected two numerals after extract");

          auto lower = std::stoll(smt2_tokenizer.get_buffer());

          if(next_token() != smt2_tokenizert::CLOSE)
            throw error("expected ')' after extract");

          auto op=operands();

          if(op.size()!=1)
            throw error("extract takes one operand");

          auto upper_e=from_integer(upper, integer_typet());
          auto lower_e=from_integer(lower, integer_typet());

          if(upper<lower)
            throw error("extract got bad indices");

          unsignedbv_typet t(upper-lower+1);

          return extractbits_exprt(op[0], upper_e, lower_e, t);
        }
        else if(id=="rotate_left" ||
                id=="rotate_right" ||
                id == ID_repeat ||
                id=="sign_extend" ||
                id=="zero_extend")
        {
          if(next_token() != smt2_tokenizert::NUMERAL)
            throw error() << "expected numeral after " << id;

          auto index = std::stoll(smt2_tokenizer.get_buffer());

          if(next_token() != smt2_tokenizert::CLOSE)
            throw error() << "expected ')' after " << id << " index";

          auto op=operands();

          if(op.size()!=1)
            throw error() << id << " takes one operand";

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
            // we first convert to a signed type of the original width,
            // then extend to the new width, and then go to unsigned
            const auto width = to_unsignedbv_type(op[0].type()).get_width();
            const signedbv_typet small_signed_type(width);
            const signedbv_typet large_signed_type(width + index);
            const unsignedbv_typet unsigned_type(width + index);

            return typecast_exprt(
              typecast_exprt(
                typecast_exprt(op[0], small_signed_type), large_signed_type),
              unsigned_type);
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
          throw error() << "unknown indexed identifier '"
                        << smt2_tokenizer.get_buffer() << '\'';
        }
      }
      else
      {
        // just double parentheses
        exprt tmp=expression();

        if(
          next_token() != smt2_tokenizert::CLOSE &&
          next_token() != smt2_tokenizert::CLOSE)
        {
          throw error("mismatched parentheses in an expression");
        }

        return tmp;
      }
    }
    else
    {
      // just double parentheses
      exprt tmp=expression();

      if(
        next_token() != smt2_tokenizert::CLOSE &&
        next_token() != smt2_tokenizert::CLOSE)
      {
        throw error("mismatched parentheses in an expression");
      }

      return tmp;
    }
    break;

  case smt2_tokenizert::CLOSE:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::NONE:
  case smt2_tokenizert::KEYWORD:
    // just parentheses
    exprt tmp=expression();
    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("mismatched parentheses in an expression");

    return tmp;
  }

  UNREACHABLE;
}

exprt smt2_parsert::expression()
{
  switch(next_token())
  {
  case smt2_tokenizert::SYMBOL:
    {
      const auto &identifier = smt2_tokenizer.get_buffer();

      // in the expression table?
      const auto e_it = expressions.find(identifier);
      if(e_it != expressions.end())
        return e_it->second();

      // rummage through id_map
      const irep_idt final_id = rename_id(identifier);
      auto id_it = id_map.find(final_id);
      if(id_it != id_map.end())
      {
        symbol_exprt symbol_expr(final_id, id_it->second.type);
        if(smt2_tokenizer.token_is_quoted_symbol())
          symbol_expr.set(ID_C_quoted, true);
        return std::move(symbol_expr);
      }

      // don't know, give up
      throw error() << "unknown expression '" << identifier << '\'';
    }

  case smt2_tokenizert::NUMERAL:
  {
    const std::string &buffer = smt2_tokenizer.get_buffer();
    if(buffer.size() >= 2 && buffer[0] == '#' && buffer[1] == 'x')
    {
      mp_integer value =
        string2integer(std::string(buffer, 2, std::string::npos), 16);
      const std::size_t width = 4 * (buffer.size() - 2);
      CHECK_RETURN(width != 0 && width % 4 == 0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else if(buffer.size() >= 2 && buffer[0] == '#' && buffer[1] == 'b')
    {
      mp_integer value =
        string2integer(std::string(buffer, 2, std::string::npos), 2);
      const std::size_t width = buffer.size() - 2;
      CHECK_RETURN(width != 0);
      unsignedbv_typet type(width);
      return from_integer(value, type);
    }
    else
    {
      return constant_exprt(buffer, integer_typet());
    }
  }

  case smt2_tokenizert::OPEN: // function application
    return function_application();

  case smt2_tokenizert::END_OF_FILE:
    throw error("EOF in an expression");

  case smt2_tokenizert::CLOSE:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::NONE:
  case smt2_tokenizert::KEYWORD:
    throw error("unexpected token in an expression");
  }

  UNREACHABLE;
}

void smt2_parsert::setup_expressions()
{
  expressions["true"] = [] { return true_exprt(); };
  expressions["false"] = [] { return false_exprt(); };

  expressions["roundNearestTiesToEven"] = [] {
    // we encode as 32-bit unsignedbv
    return from_integer(ieee_floatt::ROUND_TO_EVEN, unsignedbv_typet(32));
  };

  expressions["roundNearestTiesToAway"] = [this]() -> exprt {
    throw error("unsupported rounding mode");
  };

  expressions["roundTowardPositive"] = [] {
    // we encode as 32-bit unsignedbv
    return from_integer(ieee_floatt::ROUND_TO_PLUS_INF, unsignedbv_typet(32));
  };

  expressions["roundTowardNegative"] = [] {
    // we encode as 32-bit unsignedbv
    return from_integer(ieee_floatt::ROUND_TO_MINUS_INF, unsignedbv_typet(32));
  };

  expressions["roundTowardZero"] = [] {
    // we encode as 32-bit unsignedbv
    return from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32));
  };

  expressions["let"] = [this] { return let_expression(); };
  expressions["exists"] = [this] { return quantifier_expression(ID_exists); };
  expressions["forall"] = [this] { return quantifier_expression(ID_forall); };
  expressions["and"] = [this] { return multi_ary(ID_and, operands()); };
  expressions["or"] = [this] { return multi_ary(ID_or, operands()); };
  expressions["xor"] = [this] { return multi_ary(ID_xor, operands()); };
  expressions["not"] = [this] { return unary(ID_not, operands()); };
  expressions["="] = [this] { return binary_predicate(ID_equal, operands()); };
  expressions["<="] = [this] { return binary_predicate(ID_le, operands()); };
  expressions[">="] = [this] { return binary_predicate(ID_ge, operands()); };
  expressions["<"] = [this] { return binary_predicate(ID_lt, operands()); };
  expressions[">"] = [this] { return binary_predicate(ID_gt, operands()); };

  expressions["bvule"] = [this] { return binary_predicate(ID_le, operands()); };

  expressions["bvsle"] = [this] {
    return binary_predicate(ID_le, cast_bv_to_signed(operands()));
  };

  expressions["bvuge"] = [this] { return binary_predicate(ID_ge, operands()); };

  expressions["bvsge"] = [this] {
    return binary_predicate(ID_ge, cast_bv_to_signed(operands()));
  };

  expressions["bvult"] = [this] { return binary_predicate(ID_lt, operands()); };

  expressions["bvslt"] = [this] {
    return binary_predicate(ID_lt, cast_bv_to_signed(operands()));
  };

  expressions["bvugt"] = [this] { return binary_predicate(ID_gt, operands()); };

  expressions["bvsgt"] = [this] {
    return binary_predicate(ID_gt, cast_bv_to_signed(operands()));
  };

  expressions["bvashr"] = [this] {
    return cast_bv_to_unsigned(binary(ID_ashr, cast_bv_to_signed(operands())));
  };

  expressions["bvlshr"] = [this] { return binary(ID_lshr, operands()); };
  expressions["bvshr"] = [this] { return binary(ID_lshr, operands()); };
  expressions["bvlshl"] = [this] { return binary(ID_shl, operands()); };
  expressions["bvashl"] = [this] { return binary(ID_shl, operands()); };
  expressions["bvshl"] = [this] { return binary(ID_shl, operands()); };
  expressions["bvand"] = [this] { return multi_ary(ID_bitand, operands()); };
  expressions["bvnand"] = [this] { return multi_ary(ID_bitnand, operands()); };
  expressions["bvor"] = [this] { return multi_ary(ID_bitor, operands()); };
  expressions["bvnor"] = [this] { return multi_ary(ID_bitnor, operands()); };
  expressions["bvxor"] = [this] { return multi_ary(ID_bitxor, operands()); };
  expressions["bvxnor"] = [this] { return multi_ary(ID_bitxnor, operands()); };
  expressions["bvnot"] = [this] { return unary(ID_bitnot, operands()); };
  expressions["bvneg"] = [this] { return unary(ID_unary_minus, operands()); };
  expressions["bvadd"] = [this] { return multi_ary(ID_plus, operands()); };
  expressions["+"] = [this] { return multi_ary(ID_plus, operands()); };
  expressions["bvsub"] = [this] { return binary(ID_minus, operands()); };
  expressions["-"] = [this] { return binary(ID_minus, operands()); };
  expressions["bvmul"] = [this] { return binary(ID_mult, operands()); };
  expressions["*"] = [this] { return binary(ID_mult, operands()); };

  expressions["bvsdiv"] = [this] {
    return cast_bv_to_unsigned(binary(ID_div, cast_bv_to_signed(operands())));
  };

  expressions["bvudiv"] = [this] { return binary(ID_div, operands()); };
  expressions["/"] = [this] { return binary(ID_div, operands()); };
  expressions["div"] = [this] { return binary(ID_div, operands()); };

  expressions["bvsrem"] = [this] {
    // 2's complement signed remainder (sign follows dividend)
    // This matches our ID_mod, and what C does since C99.
    return cast_bv_to_unsigned(binary(ID_mod, cast_bv_to_signed(operands())));
  };

  expressions["bvsmod"] = [this] {
    // 2's complement signed remainder (sign follows divisor)
    // We don't have that.
    return cast_bv_to_unsigned(binary(ID_mod, cast_bv_to_signed(operands())));
  };

  expressions["bvurem"] = [this] { return binary(ID_mod, operands()); };

  expressions["%"] = [this] { return binary(ID_mod, operands()); };

  expressions["concat"] = [this] {
    auto op = operands();

    // add the widths
    auto op_width = make_range(op).map(
      [](const exprt &o) { return to_unsignedbv_type(o.type()).get_width(); });

    const std::size_t total_width =
      std::accumulate(op_width.begin(), op_width.end(), 0);

    return concatenation_exprt(std::move(op), unsignedbv_typet(total_width));
  };

  expressions["distinct"] = [this] {
    // pair-wise different constraint, multi-ary
    return multi_ary("distinct", operands());
  };

  expressions["ite"] = [this] {
    auto op = operands();

    if(op.size() != 3)
      throw error("ite takes three operands");

    if(op[0].type().id() != ID_bool)
      throw error("ite takes a boolean as first operand");

    if(op[1].type() != op[2].type())
      throw error("ite needs matching types");

    return if_exprt(op[0], op[1], op[2]);
  };

  expressions["implies"] = [this] { return binary(ID_implies, operands()); };

  expressions["=>"] = [this] { return binary(ID_implies, operands()); };

  expressions["select"] = [this] {
    auto op = operands();

    // array index
    if(op.size() != 2)
      throw error("select takes two operands");

    if(op[0].type().id() != ID_array)
      throw error("select expects array operand");

    return index_exprt(op[0], op[1]);
  };

  expressions["store"] = [this] {
    auto op = operands();

    // array update
    if(op.size() != 3)
      throw error("store takes three operands");

    if(op[0].type().id() != ID_array)
      throw error("store expects array operand");

    if(to_array_type(op[0].type()).subtype() != op[2].type())
      throw error("store expects value that matches array element type");

    return with_exprt(op[0], op[1], op[2]);
  };

  expressions["fp.isNaN"] = [this] {
    auto op = operands();

    if(op.size() != 1)
      throw error("fp.isNaN takes one operand");

    if(op[0].type().id() != ID_floatbv)
      throw error("fp.isNaN takes FloatingPoint operand");

    return unary_predicate_exprt(ID_isnan, op[0]);
  };

  expressions["fp.isInf"] = [this] {
    auto op = operands();

    if(op.size() != 1)
      throw error("fp.isInf takes one operand");

    if(op[0].type().id() != ID_floatbv)
      throw error("fp.isInf takes FloatingPoint operand");

    return unary_predicate_exprt(ID_isinf, op[0]);
  };

  expressions["fp.isNormal"] = [this] {
    auto op = operands();

    if(op.size() != 1)
      throw error("fp.isNormal takes one operand");

    if(op[0].type().id() != ID_floatbv)
      throw error("fp.isNormal takes FloatingPoint operand");

    return isnormal_exprt(op[0]);
  };

  expressions["fp"] = [this] { return function_application_fp(operands()); };

  expressions["fp.add"] = [this] {
    return function_application_ieee_float_op("fp.add", operands());
  };

  expressions["fp.mul"] = [this] {
    return function_application_ieee_float_op("fp.mul", operands());
  };

  expressions["fp.sub"] = [this] {
    return function_application_ieee_float_op("fp.sub", operands());
  };

  expressions["fp.div"] = [this] {
    return function_application_ieee_float_op("fp.div", operands());
  };

  expressions["fp.eq"] = [this] {
    return function_application_ieee_float_eq(operands());
  };

  expressions["fp.leq"] = [this] {
    return binary_predicate(ID_le, operands());
  };

  expressions["fp.lt"] = [this] { return binary_predicate(ID_lt, operands()); };

  expressions["fp.geq"] = [this] {
    return binary_predicate(ID_ge, operands());
  };

  expressions["fp.gt"] = [this] { return binary_predicate(ID_gt, operands()); };

  expressions["fp.neg"] = [this] { return unary(ID_unary_minus, operands()); };
}

typet smt2_parsert::sort()
{
  // a sort is one of the following three cases:
  // SYMBOL
  // ( _ SYMBOL ...
  // ( SYMBOL ...
  switch(next_token())
  {
  case smt2_tokenizert::SYMBOL:
    break;

  case smt2_tokenizert::OPEN:
    if(smt2_tokenizer.next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol after '(' in a sort ");

    if(smt2_tokenizer.get_buffer() == "_")
    {
      if(next_token() != smt2_tokenizert::SYMBOL)
        throw error("expected symbol after '_' in a sort");
    }
    break;

  case smt2_tokenizert::CLOSE:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::STRING_LITERAL:
  case smt2_tokenizert::NONE:
  case smt2_tokenizert::KEYWORD:
    throw error() << "unexpected token in a sort: '"
                  << smt2_tokenizer.get_buffer() << '\'';

  case smt2_tokenizert::END_OF_FILE:
    throw error() << "unexpected end-of-file in a sort";
  }

  // now we have a SYMBOL
  const auto &token = smt2_tokenizer.get_buffer();

  const auto s_it = sorts.find(token);

  if(s_it == sorts.end())
    throw error() << "unexpected sort: '" << token << '\'';

  return s_it->second();
}

void smt2_parsert::setup_sorts()
{
  sorts["Bool"] = [] { return bool_typet(); };
  sorts["Int"] = [] { return integer_typet(); };
  sorts["Real"] = [] { return real_typet(); };

  sorts["BitVec"] = [this] {
    if(next_token() != smt2_tokenizert::NUMERAL)
      throw error("expected numeral as bit-width");

    auto width = std::stoll(smt2_tokenizer.get_buffer());

    // eat the ')'
    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of sort");

    return unsignedbv_typet(width);
  };

  sorts["FloatingPoint"] = [this] {
    if(next_token() != smt2_tokenizert::NUMERAL)
      throw error("expected numeral as bit-width");

    const auto width_e = std::stoll(smt2_tokenizer.get_buffer());

    if(next_token() != smt2_tokenizert::NUMERAL)
      throw error("expected numeral as bit-width");

    const auto width_f = std::stoll(smt2_tokenizer.get_buffer());

    // consume the ')'
    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of sort");

    return ieee_float_spect(width_f - 1, width_e).to_type();
  };

  sorts["Array"] = [this] {
    // this gets two sorts as arguments, domain and range
    auto domain = sort();
    auto range = sort();

    // eat the ')'
    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of Array sort");

    // we can turn arrays that map an unsigned bitvector type
    // to something else into our 'array_typet'
    if(domain.id() == ID_unsignedbv)
      return array_typet(range, infinity_exprt(domain));
    else
      throw error("unsupported array sort");
  };
}

smt2_parsert::signature_with_parameter_idst
smt2_parsert::function_signature_definition()
{
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  if(smt2_tokenizer.peek() == smt2_tokenizert::CLOSE)
  {
    // no parameters
    next_token(); // eat the ')'
    return signature_with_parameter_idst(sort());
  }

  mathematical_function_typet::domaint domain;
  std::vector<irep_idt> parameters;

  while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
  {
    if(next_token() != smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    irep_idt id = smt2_tokenizer.get_buffer();
    domain.push_back(sort());

    parameters.push_back(
      add_fresh_id(id, idt::PARAMETER, exprt(ID_nil, domain.back())));

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  next_token(); // eat the ')'

  typet codomain = sort();

  return signature_with_parameter_idst(
    mathematical_function_typet(domain, codomain), parameters);
}

typet smt2_parsert::function_signature_declaration()
{
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  if(smt2_tokenizer.peek() == smt2_tokenizert::CLOSE)
  {
    next_token(); // eat the ')'
    return sort();
  }

  mathematical_function_typet::domaint domain;

  while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
  {
    if(next_token() != smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    domain.push_back(sort());

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  next_token(); // eat the ')'

  typet codomain = sort();

  return mathematical_function_typet(domain, codomain);
}

void smt2_parsert::command(const std::string &c)
{
  auto c_it = commands.find(c);
  if(c_it == commands.end())
  {
    // silently ignore
    ignore_command();
  }
  else
    c_it->second();
}

void smt2_parsert::setup_commands()
{
  commands["declare-const"] = [this]() {
    const auto s = smt2_tokenizer.get_buffer();

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol after " << s;

    irep_idt id = smt2_tokenizer.get_buffer();
    auto type = sort();

    add_unique_id(id, exprt(ID_nil, type));
  };

  // declare-var appears to be a synonym for declare-const that is
  // accepted by Z3 and CVC4
  commands["declare-var"] = commands["declare-const"];

  commands["declare-fun"] = [this]() {
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-fun");

    irep_idt id = smt2_tokenizer.get_buffer();
    auto type = function_signature_declaration();

    add_unique_id(id, exprt(ID_nil, type));
  };

  commands["define-const"] = [this]() {
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-const");

    const irep_idt id = smt2_tokenizer.get_buffer();

    const auto type = sort();
    const auto value = expression();

    // check type of value
    if(value.type() != type)
    {
      throw error() << "type mismatch in constant definition: expected '"
                    << smt2_format(type) << "' but got '"
                    << smt2_format(value.type()) << '\'';
    }

    // create the entry
    add_unique_id(id, value);
  };

  commands["define-fun"] = [this]() {
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");

    // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;

    const irep_idt id = smt2_tokenizer.get_buffer();

    const auto signature = function_signature_definition();
    const auto body = expression();

    // restore renamings
    std::swap(renaming_map, old_renaming_map);

    // check type of body
    if(signature.type.id() == ID_mathematical_function)
    {
      const auto &f_signature = to_mathematical_function_type(signature.type);
      if(body.type() != f_signature.codomain())
      {
        throw error() << "type mismatch in function definition: expected '"
                      << smt2_format(f_signature.codomain()) << "' but got '"
                      << smt2_format(body.type()) << '\'';
      }
    }
    else if(body.type() != signature.type)
    {
      throw error() << "type mismatch in function definition: expected '"
                    << smt2_format(signature.type) << "' but got '"
                    << smt2_format(body.type()) << '\'';
    }

    // create the entry
    add_unique_id(id, body);

    id_map.at(id).type = signature.type;
    id_map.at(id).parameters = signature.parameters;
  };

  commands["exit"] = [this]() { exit = true; };
}
