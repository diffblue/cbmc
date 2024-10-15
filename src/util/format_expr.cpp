/*******************************************************************\

Module: Expression Pretty Printing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Pretty Printing

#include "format_expr.h"

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "byte_operators.h"
#include "expr_util.h"
#include "floatbv_expr.h"
#include "format_type.h"
#include "ieee_float.h"
#include "mathematical_expr.h"
#include "mp_arith.h"
#include "pointer_expr.h"
#include "string_utils.h"

#include <map>
#include <ostream>

// expressions that are rendered with infix operators
struct infix_opt
{
  const char *rep;
};

const std::map<irep_idt, infix_opt> infix_map = {
  {ID_plus, {"+"}},
  {ID_minus, {"-"}},
  {ID_mult, {"*"}},
  {ID_div, {"/"}},
  {ID_equal, {"="}},
  {ID_notequal, {u8"\u2260"}}, // /=, U+2260
  {ID_and, {u8"\u2227"}},      // wedge, U+2227
  {ID_or, {u8"\u2228"}},       // vee, U+2228
  {ID_xor, {u8"\u2295"}},      // + in circle, U+2295
  {ID_implies, {u8"\u21d2"}},  // =>, U+21D2
  {ID_le, {u8"\u2264"}},       // <=, U+2264
  {ID_ge, {u8"\u2265"}},       // >=, U+2265
  {ID_lt, {"<"}},
  {ID_gt, {">"}},
};

/// We use the precendences that most readers expect
/// (i.e., the ones you learn in primary school),
/// and stay clear of the surprising ones that C has.
static bool bracket_subexpression(const exprt &sub_expr, const exprt &expr)
{
  // no need for parentheses whenever the subexpression
  // doesn't have operands
  if(!sub_expr.has_operands())
    return false;

  // no need if subexpression isn't an infix operator
  if(infix_map.find(sub_expr.id()) == infix_map.end())
    return false;

  // * and / bind stronger than + and -
  if(
    (sub_expr.id() == ID_mult || sub_expr.id() == ID_div) &&
    (expr.id() == ID_plus || expr.id() == ID_minus))
    return false;

  // ==, !=, <, <=, >, >= bind stronger than && and ||
  if(
    (sub_expr.id() == ID_equal || sub_expr.id() == ID_notequal ||
     sub_expr.id() == ID_lt || sub_expr.id() == ID_gt ||
     sub_expr.id() == ID_le || sub_expr.id() == ID_ge) &&
    (expr.id() == ID_and || expr.id() == ID_or))
    return false;

  // +, -, *, / bind stronger than ==, !=, <, <=, >, >=
  if(
    (sub_expr.id() == ID_plus || sub_expr.id() == ID_minus ||
     sub_expr.id() == ID_mult || sub_expr.id() == ID_div) &&
    (expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_lt ||
     expr.id() == ID_gt || expr.id() == ID_le || expr.id() == ID_ge))
  {
    return false;
  }

  return true;
}

/// This formats a multi-ary expression,
/// adding parentheses where indicated by \ref bracket_subexpression
static std::ostream &format_rec(std::ostream &os, const multi_ary_exprt &src)
{
  bool first = true;

  std::string operator_str = id2string(src.id()); // default

  if(src.id() == ID_equal && to_equal_expr(src).op0().is_boolean())
  {
    operator_str = u8"\u21d4"; // <=>, U+21D4
  }
  else
  {
    auto infix_map_it = infix_map.find(src.id());
    if(infix_map_it != infix_map.end())
      operator_str = infix_map_it->second.rep;
  }

  for(const auto &op : src.operands())
  {
    if(first)
      first = false;
    else
      os << ' ' << operator_str << ' ';

    const bool need_parentheses = bracket_subexpression(op, src);

    if(need_parentheses)
      os << '(';

    os << format(op);

    if(need_parentheses)
      os << ')';
  }

  return os;
}

/// This formats a binary expression,
/// which we do as for multi-ary expressions
static std::ostream &format_rec(std::ostream &os, const binary_exprt &src)
{
  return format_rec(os, to_multi_ary_expr(src));
}

/// This formats a unary expression,
/// adding parentheses very aggressively.
static std::ostream &format_rec(std::ostream &os, const unary_exprt &src)
{
  if(src.id() == ID_not)
    os << u8"\u00ac"; // neg, U+00AC
  else if(src.id() == ID_unary_minus)
    os << '-';
  else if(src.id() == ID_count_leading_zeros)
    os << "clz";
  else if(src.id() == ID_count_trailing_zeros)
    os << "ctz";
  else if(src.id() == ID_find_first_set)
    os << "ffs";
  else
    return os << src.pretty();

  if(src.op().has_operands())
    return os << '(' << format(src.op()) << ')';
  else
    return os << format(src.op());
}

/// This formats a ternary expression
static std::ostream &format_rec(std::ostream &os, const ternary_exprt &src)
{
  os << src.id() << '(' << format(src.op0()) << ", " << format(src.op1())
     << ", " << format(src.op2()) << ')';
  return os;
}

/// This formats a constant
static std::ostream &format_rec(std::ostream &os, const constant_exprt &src)
{
  auto type = src.type().id();

  if(type == ID_bool)
  {
    if(src.is_true())
      return os << "true";
    else if(src.is_false())
      return os << "false";
    else
      return os << src.pretty();
  }
  else if(
    type == ID_unsignedbv || type == ID_signedbv || type == ID_c_bool ||
    type == ID_c_bit_field)
    return os << *numeric_cast<mp_integer>(src);
  else if(type == ID_bv)
  {
    // These do not have a numerical interpretation.
    // We'll print the 0/1 bit pattern, starting with the bit
    // that has the highest index.
    auto width = to_bv_type(src.type()).get_width();
    std::string result;
    result.reserve(width);
    auto &value = src.get_value();
    for(std::size_t i = 0; i < width; i++)
      result += get_bvrep_bit(value, width, width - i - 1) ? '1' : '0';
    return os << result;
  }
  else if(type == ID_integer || type == ID_natural || type == ID_range)
    return os << src.get_value();
  else if(type == ID_string)
    return os << '"' << escape(id2string(src.get_value())) << '"';
  else if(type == ID_floatbv)
    return os << ieee_floatt(src);
  else if(type == ID_pointer)
  {
    if(src.is_null_pointer())
      return os << ID_NULL;
    else if(
      src.get_value() == "INVALID" || src.get_value().starts_with("INVALID-"))
    {
      return os << "INVALID-POINTER";
    }
    else
    {
      const auto &pointer_type = to_pointer_type(src.type());
      const auto width = pointer_type.get_width();
      auto int_value = bvrep2integer(src.get_value(), width, false);
      return os << "pointer(0x" << integer2string(int_value, 16) << ", "
                << format(pointer_type.base_type()) << ')';
    }
  }
  else if(type == ID_c_enum_tag)
  {
    return os << string2integer(id2string(src.get_value()), 16);
  }
  else
    return os << src.pretty();
}

std::ostream &fallback_format_rec(std::ostream &os, const exprt &expr)
{
  os << expr.id();

  for(const auto &s : expr.get_named_sub())
    if(s.first != ID_type && s.first != ID_C_source_location)
      os << ' ' << s.first << "=\"" << s.second.id() << '"';

  if(expr.has_operands())
  {
    os << '(';
    bool first = true;

    for(const auto &op : expr.operands())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(op);
    }

    os << ')';
  }

  return os;
}

class format_expr_configt
{
public:
  format_expr_configt()
  {
    setup();
  }

  using formattert =
    std::function<std::ostream &(std::ostream &, const exprt &)>;
  using expr_mapt = std::unordered_map<irep_idt, formattert>;

  expr_mapt expr_map;

  /// find the formatter for a given expression
  const formattert &find_formatter(const exprt &);

private:
  /// setup the expressions we can format
  void setup();

  formattert fallback;
};

// The below generates textual output in a generic syntax
// that is inspired by C/C++/Java, and is meant for debugging
// purposes.
void format_expr_configt::setup()
{
  auto multi_ary_expr =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, to_multi_ary_expr(expr));
  };

  expr_map[ID_plus] = multi_ary_expr;
  expr_map[ID_mult] = multi_ary_expr;
  expr_map[ID_and] = multi_ary_expr;
  expr_map[ID_or] = multi_ary_expr;
  expr_map[ID_xor] = multi_ary_expr;

  auto binary_infix_expr =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, to_binary_expr(expr));
  };

  expr_map[ID_lt] = binary_infix_expr;
  expr_map[ID_gt] = binary_infix_expr;
  expr_map[ID_ge] = binary_infix_expr;
  expr_map[ID_le] = binary_infix_expr;
  expr_map[ID_div] = binary_infix_expr;
  expr_map[ID_minus] = binary_infix_expr;
  expr_map[ID_implies] = binary_infix_expr;
  expr_map[ID_equal] = binary_infix_expr;
  expr_map[ID_notequal] = binary_infix_expr;

  auto binary_prefix_expr =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    os << expr.id() << '(' << format(to_binary_expr(expr).op0()) << ", "
       << format(to_binary_expr(expr).op1()) << ')';
    return os;
  };

  expr_map[ID_ieee_float_equal] = binary_prefix_expr;
  expr_map[ID_ieee_float_notequal] = binary_prefix_expr;

  auto unary_expr = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, to_unary_expr(expr));
  };

  expr_map[ID_not] = unary_expr;
  expr_map[ID_unary_minus] = unary_expr;

  auto unary_with_parentheses_expr =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return os << expr.id() << '(' << format(to_unary_expr(expr).op()) << ')';
  };

  expr_map[ID_isnan] = unary_with_parentheses_expr;
  expr_map[ID_isinf] = unary_with_parentheses_expr;
  expr_map[ID_isfinite] = unary_with_parentheses_expr;
  expr_map[ID_isnormal] = unary_with_parentheses_expr;

  auto ternary_expr =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, to_ternary_expr(expr));
  };

  expr_map[ID_floatbv_plus] = ternary_expr;
  expr_map[ID_floatbv_minus] = ternary_expr;
  expr_map[ID_floatbv_mult] = ternary_expr;
  expr_map[ID_floatbv_div] = ternary_expr;
  expr_map[ID_floatbv_mod] = binary_infix_expr;
  expr_map[ID_floatbv_rem] = binary_infix_expr;

  expr_map[ID_constant] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, to_constant_expr(expr));
  };

  expr_map[ID_address_of] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &address_of = to_address_of_expr(expr);
    return os << "address_of(" << format(address_of.object()) << ')';
  };

  expr_map[ID_annotated_pointer_constant] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &annotated_pointer = to_annotated_pointer_constant_expr(expr);
    return os << format(annotated_pointer.symbolic_pointer());
  };

  expr_map[ID_typecast] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return os << "cast(" << format(to_typecast_expr(expr).op()) << ", "
              << format(expr.type()) << ')';
  };

  expr_map[ID_floatbv_typecast] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &floatbv_typecast_expr = to_floatbv_typecast_expr(expr);
    return os << "floatbv_typecast(" << format(floatbv_typecast_expr.op())
              << ", " << format(floatbv_typecast_expr.type()) << ", "
              << format(floatbv_typecast_expr.rounding_mode()) << ')';
  };

  auto byte_extract =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &byte_extract_expr = to_byte_extract_expr(expr);
    return os << expr.id() << '(' << format(byte_extract_expr.op()) << ", "
              << format(byte_extract_expr.offset()) << ", "
              << format(byte_extract_expr.type()) << ')';
  };

  expr_map[ID_byte_extract_little_endian] = byte_extract;
  expr_map[ID_byte_extract_big_endian] = byte_extract;

  auto byte_update = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &byte_update_expr = to_byte_update_expr(expr);
    return os << expr.id() << '(' << format(byte_update_expr.op()) << ", "
              << format(byte_update_expr.offset()) << ", "
              << format(byte_update_expr.value()) << ", "
              << format(byte_update_expr.type()) << ')';
  };

  expr_map[ID_byte_update_little_endian] = byte_update;
  expr_map[ID_byte_update_big_endian] = byte_update;

  expr_map[ID_member] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return os << format(to_member_expr(expr).op()) << '.'
              << to_member_expr(expr).get_component_name();
  };

  expr_map[ID_symbol] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return os << to_symbol_expr(expr).get_identifier();
  };

  expr_map[ID_index] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &index_expr = to_index_expr(expr);
    return os << format(index_expr.array()) << '[' << format(index_expr.index())
              << ']';
  };

  expr_map[ID_type] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return format_rec(os, expr.type());
  };

  expr_map[ID_forall] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    os << u8"\u2200 ";
    bool first = true;
    for(const auto &symbol : to_quantifier_expr(expr).variables())
    {
      if(first)
        first = false;
      else
        os << ", ";
      os << format(symbol) << " : " << format(symbol.type());
    }
    return os << " . " << format(to_quantifier_expr(expr).where());
  };

  expr_map[ID_exists] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    os << u8"\u2203 ";
    bool first = true;
    for(const auto &symbol : to_quantifier_expr(expr).variables())
    {
      if(first)
        first = false;
      else
        os << ", ";
      os << format(symbol) << " : " << format(symbol.type());
    }
    return os << " . " << format(to_quantifier_expr(expr).where());
  };

  expr_map[ID_let] = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &let_expr = to_let_expr(expr);

    os << "LET ";

    bool first = true;

    const auto &values = let_expr.values();
    auto values_it = values.begin();
    for(auto &v : let_expr.variables())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(v) << " = " << format(*values_it);
      ++values_it;
    }

    return os << " IN " << format(let_expr.where());
  };

  expr_map[ID_lambda] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &lambda_expr = to_lambda_expr(expr);

    os << u8"\u03bb ";

    bool first = true;

    for(auto &v : lambda_expr.variables())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(v);
    }

    return os << " . " << format(lambda_expr.where());
  };

  auto compound = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    os << "{ ";

    bool first = true;

    for(const auto &op : expr.operands())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(op);
    }

    return os << " }";
  };

  expr_map[ID_array] = compound;
  expr_map[ID_struct] = compound;

  expr_map[ID_array_of] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &array_of_expr = to_array_of_expr(expr);
    return os << "array_of(" << format(array_of_expr.what()) << ')';
  };

  expr_map[ID_if] = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &if_expr = to_if_expr(expr);
    return os << '(' << format(if_expr.cond()) << " ? "
              << format(if_expr.true_case()) << " : "
              << format(if_expr.false_case()) << ')';
  };

  expr_map[ID_string_constant] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return os << '"' << expr.get_string(ID_value) << '"';
  };

  expr_map[ID_function_application] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &function_application_expr = to_function_application_expr(expr);
    os << format(function_application_expr.function()) << '(';
    bool first = true;
    for(auto &argument : function_application_expr.arguments())
    {
      if(first)
        first = false;
      else
        os << ", ";
      os << format(argument);
    }
    os << ')';
    return os;
  };

  expr_map[ID_dereference] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &dereference_expr = to_dereference_expr(expr);
    os << '*';
    if(dereference_expr.pointer().id() != ID_symbol)
      os << '(' << format(dereference_expr.pointer()) << ')';
    else
      os << format(dereference_expr.pointer());
    return os;
  };

  expr_map[ID_saturating_minus] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &saturating_minus = to_saturating_minus_expr(expr);
    return os << "saturating-(" << format(saturating_minus.lhs()) << ", "
              << format(saturating_minus.rhs()) << ')';
  };

  expr_map[ID_saturating_plus] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &saturating_plus = to_saturating_plus_expr(expr);
    return os << "saturating+(" << format(saturating_plus.lhs()) << ", "
              << format(saturating_plus.rhs()) << ')';
  };

  expr_map[ID_object_address] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &object_address_expr = to_object_address_expr(expr);
    return os << u8"\u275d" << object_address_expr.object_identifier()
              << u8"\u275e";
  };

  expr_map[ID_object_size] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &object_size_expr = to_object_size_expr(expr);
    return os << "object_size(" << format(object_size_expr.op()) << ')';
  };

  expr_map[ID_pointer_offset] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &pointer_offset_expr = to_pointer_offset_expr(expr);
    return os << "pointer_offset(" << format(pointer_offset_expr.op()) << ')';
  };

  expr_map[ID_field_address] =
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
    const auto &field_address_expr = to_field_address_expr(expr);
    return os << format(field_address_expr.base()) << u8".\u275d"
              << field_address_expr.component_name() << u8"\u275e";
  };

  fallback = [](std::ostream &os, const exprt &expr) -> std::ostream & {
    return fallback_format_rec(os, expr);
  };
}

const format_expr_configt::formattert &
format_expr_configt::find_formatter(const exprt &expr)
{
  auto m_it = expr_map.find(expr.id());
  if(m_it == expr_map.end())
    return fallback;
  else
    return m_it->second;
}

format_expr_configt format_expr_config;

void add_format_hook(irep_idt id, format_expr_configt::formattert formatter)
{
  format_expr_config.expr_map[id] = std::move(formatter);
}

std::ostream &format_rec(std::ostream &os, const exprt &expr)
{
  auto &formatter = format_expr_config.find_formatter(expr);
  return formatter(os, expr);
}
