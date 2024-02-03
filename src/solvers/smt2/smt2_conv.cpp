/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SMT Backend

#include "smt2_conv.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/fixedbv.h>
#include <util/floatbv_expr.h>
#include <util/format_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_constant.h>
#include <util/threeval.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>
#include <solvers/prop/literal_expr.h>

#include "smt2_tokenizer.h"

#include <cstdint>

// Mark different kinds of error conditions

// Unexpected types and other combinations not implemented and not
// expected to be needed
#define UNEXPECTEDCASE(S) PRECONDITION_WITH_DIAGNOSTICS(false, S);

// General todos
#define SMT2_TODO(S) PRECONDITION_WITH_DIAGNOSTICS(false, "TODO: " S)

smt2_convt::smt2_convt(
  const namespacet &_ns,
  const std::string &_benchmark,
  const std::string &_notes,
  const std::string &_logic,
  solvert _solver,
  std::ostream &_out)
  : use_FPA_theory(false),
    use_array_of_bool(false),
    use_as_const(false),
    use_check_sat_assuming(false),
    use_datatypes(false),
    use_lambda_for_array(false),
    emit_set_logic(true),
    ns(_ns),
    out(_out),
    benchmark(_benchmark),
    notes(_notes),
    logic(_logic),
    solver(_solver),
    boolbv_width(_ns),
    pointer_logic(_ns),
    no_boolean_variables(0)
{
  // We set some defaults differently
  // for some solvers.

  switch(solver)
  {
  case solvert::GENERIC:
    break;

  case solvert::BITWUZLA:
    use_FPA_theory = true;
    use_array_of_bool = true;
    use_as_const = true;
    use_check_sat_assuming = true;
    use_lambda_for_array = true;
    emit_set_logic = false;
    break;

  case solvert::BOOLECTOR:
    break;

  case solvert::CPROVER_SMT2:
    use_FPA_theory = true;
    use_array_of_bool = true;
    use_as_const = true;
    use_check_sat_assuming = true;
    emit_set_logic = false;
    break;

  case solvert::CVC3:
    break;

  case solvert::CVC4:
    logic = "ALL";
    use_array_of_bool = true;
    use_as_const = true;
    break;

  case solvert::CVC5:
    logic = "ALL";
    use_FPA_theory = true;
    use_array_of_bool = true;
    use_as_const = true;
    use_check_sat_assuming = true;
    use_datatypes = true;
    break;

  case solvert::MATHSAT:
    break;

  case solvert::YICES:
    break;

  case solvert::Z3:
    use_array_of_bool = true;
    use_as_const = true;
    use_check_sat_assuming = true;
    use_lambda_for_array = true;
    emit_set_logic = false;
    use_datatypes = true;
    break;
  }

  write_header();
}

std::string smt2_convt::decision_procedure_text() const
{
  return "SMT2";
}

void smt2_convt::print_assignment(std::ostream &os) const
{
  // Boolean stuff

  for(std::size_t v=0; v<boolean_assignment.size(); v++)
    os << "b" << v << "=" << boolean_assignment[v] << "\n";

  // others
}

tvt smt2_convt::l_get(literalt l) const
{
  if(l.is_true())
    return tvt(true);
  if(l.is_false())
    return tvt(false);

  INVARIANT(
    l.var_no() < boolean_assignment.size(),
    "variable number shall be within bounds");
  return tvt(boolean_assignment[l.var_no()]^l.sign());
}

void smt2_convt::write_header()
{
  out << "; SMT 2" << "\n";

  switch(solver)
  {
  // clang-format off
  case solvert::GENERIC: break;
  case solvert::BITWUZLA: out << "; Generated for Bitwuzla\n"; break;
  case solvert::BOOLECTOR: out << "; Generated for Boolector\n"; break;
  case solvert::CPROVER_SMT2:
    out << "; Generated for the CPROVER SMT2 solver\n"; break;
  case solvert::CVC3: out << "; Generated for CVC 3\n"; break;
  case solvert::CVC4: out << "; Generated for CVC 4\n"; break;
  case solvert::CVC5: out << "; Generated for CVC 5\n"; break;
  case solvert::MATHSAT: out << "; Generated for MathSAT\n"; break;
  case solvert::YICES: out << "; Generated for Yices\n"; break;
  case solvert::Z3: out << "; Generated for Z3\n"; break;
    // clang-format on
  }

  out << "(set-info :source \"" << notes << "\")" << "\n";

  out << "(set-option :produce-models true)" << "\n";

  // We use a broad mixture of logics, so on some solvers
  // its better not to declare here.
  // set-logic should come after setting options
  if(emit_set_logic && !logic.empty())
    out << "(set-logic " << logic << ")" << "\n";
}

void smt2_convt::write_footer()
{
  out << "\n";

  // fix up the object sizes
  for(const auto &object : object_sizes)
    define_object_size(object.second, object.first);

  if(use_check_sat_assuming && !assumptions.empty())
  {
    out << "(check-sat-assuming (";
    for(const auto &assumption : assumptions)
      convert_literal(to_literal_expr(assumption).get_literal());
    out << "))\n";
  }
  else
  {
    // add the assumptions, if any
    if(!assumptions.empty())
    {
      out << "; assumptions\n";

      for(const auto &assumption : assumptions)
      {
        out << "(assert ";
        convert_literal(to_literal_expr(assumption).get_literal());
        out << ")"
            << "\n";
      }
    }

    out << "(check-sat)\n";
  }

  out << "\n";

  if(solver!=solvert::BOOLECTOR)
  {
    for(const auto &id : smt2_identifiers)
      out << "(get-value (" << id << "))"
          << "\n";
  }

  out << "\n";

  out << "(exit)\n";

  out << "; end of SMT2 file"
      << "\n";
}

/// Returns true iff \p type has effective width of zero bits.
static bool is_zero_width(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_empty)
    return true;
  else if(type.id() == ID_struct_tag)
    return is_zero_width(ns.follow_tag(to_struct_tag_type(type)), ns);
  else if(type.id() == ID_union_tag)
    return is_zero_width(ns.follow_tag(to_union_tag_type(type)), ns);
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &comp : to_struct_union_type(type).components())
    {
      if(!is_zero_width(comp.type(), ns))
        return false;
    }
    return true;
  }
  else if(auto array_type = type_try_dynamic_cast<array_typet>(type))
  {
    // we ignore array_type->size().is_zero() for now as there may be
    // out-of-bounds accesses that we need to model
    return is_zero_width(array_type->element_type(), ns);
  }
  else
    return false;
}

void smt2_convt::define_object_size(
  const irep_idt &id,
  const object_size_exprt &expr)
{
  const exprt &ptr = expr.pointer();
  std::size_t pointer_width = boolbv_width(ptr.type());
  std::size_t number = 0;
  std::size_t h=pointer_width-1;
  std::size_t l=pointer_width-config.bv_encoding.object_bits;

  for(const auto &o : pointer_logic.objects)
  {
    const typet &type = o.type();
    auto size_expr = size_of_expr(type, ns);

    if(
      (o.id() != ID_symbol && o.id() != ID_string_constant) ||
      !size_expr.has_value())
    {
      ++number;
      continue;
    }

    find_symbols(*size_expr);
    out << "(assert (=> (= "
        << "((_ extract " << h << " " << l << ") ";
    convert_expr(ptr);
    out << ") (_ bv" << number << " " << config.bv_encoding.object_bits << "))"
        << "(= " << id << " ";
    convert_expr(*size_expr);
    out << ")))\n";

    ++number;
  }
}

decision_proceduret::resultt smt2_convt::dec_solve(const exprt &assumption)
{
  if(assumption.is_nil())
    write_footer();
  else
  {
    assumptions.push_back(literal_exprt(convert(assumption)));
    write_footer();
    assumptions.pop_back();
  }

  out.flush();
  return decision_proceduret::resultt::D_ERROR;
}

exprt smt2_convt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(expr).get_identifier();

    identifier_mapt::const_iterator it=identifier_map.find(id);

    if(it!=identifier_map.end())
      return it->second.value;
    return expr;
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id=to_nondet_symbol_expr(expr).get_identifier();

    identifier_mapt::const_iterator it=identifier_map.find(id);

    if(it!=identifier_map.end())
      return it->second.value;
  }
  else if(expr.id() == ID_literal)
  {
    auto l = to_literal_expr(expr).get_literal();
    if(l_get(l).is_true())
      return true_exprt();
    else
      return false_exprt();
  }
  else if(expr.id() == ID_not)
  {
    auto op = get(to_not_expr(expr).op());
    if(op.is_true())
      return false_exprt();
    else if(op.is_false())
      return true_exprt();
  }
  else if(
    expr.is_constant() || expr.id() == ID_empty_union ||
    (!expr.has_operands() && (expr.id() == ID_struct || expr.id() == ID_array)))
  {
    return expr;
  }
  else if(expr.has_operands())
  {
    exprt copy = expr;
    for(auto &op : copy.operands())
    {
      exprt eval_op = get(op);
      if(eval_op.is_nil())
        return nil_exprt{};
      op = std::move(eval_op);
    }
    return copy;
  }

  return nil_exprt();
}

constant_exprt smt2_convt::parse_literal(
  const irept &src,
  const typet &type)
{
  // See http://www.grammatech.com/resources/smt/SMTLIBTutorial.pdf for the
  // syntax of SMTlib2 literals.
  //
  // A literal expression is one of the following forms:
  //
  // * Numeral -- this is a natural number in decimal and is of the form:
  //                0|([1-9][0-9]*)
  // * Decimal -- this is a decimal expansion of a real number of the form:
  //                (0|[1-9][0-9]*)[.]([0-9]+)
  // * Binary -- this is a natural number in binary and is of the form:
  //                #b[01]+
  // * Hex -- this is a natural number in hexadecimal and is of the form:
  //                #x[0-9a-fA-F]+
  //
  // Right now I'm not parsing decimals.  It'd be nice if we had a real YACC
  // parser here, but whatever.

  mp_integer value;

  if(!src.id().empty())
  {
    const std::string &s=src.id_string();

    if(s.size()>=2 && s[0]=='#' && s[1]=='b')
    {
      // Binary #b010101
      value=string2integer(s.substr(2), 2);
    }
    else if(s.size()>=2 && s[0]=='#' && s[1]=='x')
    {
      // Hex #x012345
      value=string2integer(s.substr(2), 16);
    }
    else
    {
      // Numeral
      value=string2integer(s);
    }
  }
  else if(src.get_sub().size()==2 &&
          src.get_sub()[0].id()=="-") // (- 100)
  {
    value=-string2integer(src.get_sub()[1].id_string());
  }
  else if(src.get_sub().size()==3 &&
          src.get_sub()[0].id()=="_" &&
          // (_ bvDECIMAL_VALUE SIZE)
          src.get_sub()[1].id_string().substr(0, 2)=="bv")
  {
    value=string2integer(src.get_sub()[1].id_string().substr(2));
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="fp") // (fp signbv exponentbv significandbv)
  {
    if(type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(type);
      constant_exprt s1 = parse_literal(src.get_sub()[1], unsignedbv_typet(1));
      constant_exprt s2 =
        parse_literal(src.get_sub()[2], unsignedbv_typet(floatbv_type.get_e()));
      constant_exprt s3 =
        parse_literal(src.get_sub()[3], unsignedbv_typet(floatbv_type.get_f()));

      const auto s1_int = numeric_cast_v<mp_integer>(s1);
      const auto s2_int = numeric_cast_v<mp_integer>(s2);
      const auto s3_int = numeric_cast_v<mp_integer>(s3);

      // stitch the bits together
      value = bitwise_or(
        s1_int << (floatbv_type.get_e() + floatbv_type.get_f()),
        bitwise_or((s2_int << floatbv_type.get_f()), s3_int));
    }
    else
      value=0;
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="+oo") // (_ +oo e s)
  {
    std::size_t e = unsafe_string2size_t(src.get_sub()[2].id_string());
    std::size_t s = unsafe_string2size_t(src.get_sub()[3].id_string());
    return ieee_floatt::plus_infinity(ieee_float_spect(s - 1, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="-oo") // (_ -oo e s)
  {
    std::size_t e = unsafe_string2size_t(src.get_sub()[2].id_string());
    std::size_t s = unsafe_string2size_t(src.get_sub()[3].id_string());
    return ieee_floatt::minus_infinity(ieee_float_spect(s - 1, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="NaN") // (_ NaN e s)
  {
    std::size_t e = unsafe_string2size_t(src.get_sub()[2].id_string());
    std::size_t s = unsafe_string2size_t(src.get_sub()[3].id_string());
    return ieee_floatt::NaN(ieee_float_spect(s - 1, e)).to_expr();
  }

  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_c_enum ||
     type.id()==ID_c_bool)
  {
    return from_integer(value, type);
  }
  else if(type.id()==ID_c_enum_tag)
  {
    constant_exprt result =
      from_integer(value, ns.follow_tag(to_c_enum_tag_type(type)));

    // restore the c_enum_tag type
    result.type() = type;
    return result;
  }
  else if(type.id()==ID_fixedbv ||
          type.id()==ID_floatbv)
  {
    std::size_t width=boolbv_width(type);
    return constant_exprt(integer2bvrep(value, width), type);
  }
  else if(type.id()==ID_integer ||
          type.id()==ID_range)
  {
    return from_integer(value, type);
  }
  else
    UNREACHABLE_BECAUSE(
      "smt2_convt::parse_literal should not be of unsupported type " +
      type.id_string());
}

exprt smt2_convt::parse_array(
  const irept &src,
  const array_typet &type)
{
  std::unordered_map<int64_t, exprt> operands_map;
  walk_array_tree(&operands_map, src, type);
  exprt::operandst operands;
  // Try to find the default value, if there is none then set it
  auto maybe_default_op = operands_map.find(-1);
  exprt default_op;
  if(maybe_default_op == operands_map.end())
    default_op = nil_exprt();
  else
    default_op = maybe_default_op->second;
  int64_t i = 0;
  auto maybe_size = numeric_cast<std::int64_t>(type.size());
  if(maybe_size.has_value())
  {
    while(i < maybe_size.value())
    {
      auto found_op = operands_map.find(i);
      if(found_op != operands_map.end())
        operands.emplace_back(found_op->second);
      else
        operands.emplace_back(default_op);
      i++;
    }
  }
  else
  {
    // Array size is unknown, keep adding with known indexes in order
    // until we fail to find one.
    auto found_op = operands_map.find(i);
    while(found_op != operands_map.end())
    {
      operands.emplace_back(found_op->second);
      i++;
      found_op = operands_map.find(i);
    }
    operands.emplace_back(default_op);
  }
  return array_exprt(operands, type);
}

void smt2_convt::walk_array_tree(
  std::unordered_map<int64_t, exprt> *operands_map,
  const irept &src,
  const array_typet &type)
{
  if(src.get_sub().size()==4 && src.get_sub()[0].id()=="store")
  {
    // This is the SMT syntax being parsed here
    // (store array index value)
    // Recurse
    walk_array_tree(operands_map, src.get_sub()[1], type);
    const auto index_expr = parse_rec(src.get_sub()[2], type.size().type());
    const constant_exprt index_constant = to_constant_expr(index_expr);
    mp_integer tempint;
    bool failure = to_integer(index_constant, tempint);
    if(failure)
      return;
    long index = tempint.to_long();
    exprt value = parse_rec(src.get_sub()[3], type.element_type());
    operands_map->emplace(index, value);
  }
  else if(src.get_sub().size()==2 &&
          src.get_sub()[0].get_sub().size()==3 &&
          src.get_sub()[0].get_sub()[0].id()=="as" &&
          src.get_sub()[0].get_sub()[1].id()=="const")
  {
    // (as const type_info default_value)
    exprt default_value = parse_rec(src.get_sub()[1], type.element_type());
    operands_map->emplace(-1, default_value);
  }
  else
  {
    auto bindings_it = current_bindings.find(src.id());
    if(bindings_it != current_bindings.end())
      walk_array_tree(operands_map, bindings_it->second, type);
  }
}

exprt smt2_convt::parse_union(
  const irept &src,
  const union_typet &type)
{
  // these are always flat
  PRECONDITION(!type.components().empty());
  const union_typet::componentt &first=type.components().front();
  std::size_t width=boolbv_width(type);
  exprt value = parse_rec(src, unsignedbv_typet(width));
  if(value.is_nil())
    return nil_exprt();
  const typecast_exprt converted(value, first.type());
  return union_exprt(first.get_name(), converted, type);
}

struct_exprt
smt2_convt::parse_struct(const irept &src, const struct_typet &type)
{
  const struct_typet::componentst &components =
    type.components();

  struct_exprt result(exprt::operandst(components.size(), nil_exprt()), type);

  if(components.empty())
    return result;

  if(use_datatypes)
  {
    // Structs look like:
    //  (mk-struct.1 <component0> <component1> ... <componentN>)
    std::size_t j = 1;
    for(std::size_t i=0; i<components.size(); i++)
    {
      const struct_typet::componentt &c=components[i];
      if(is_zero_width(components[i].type(), ns))
      {
        result.operands()[i] = nil_exprt{};
      }
      else
      {
        DATA_INVARIANT(
          src.get_sub().size() > j, "insufficient number of component values");
        result.operands()[i] = parse_rec(src.get_sub()[j], c.type());
        ++j;
      }
    }
  }
  else
  {
    // These are just flattened, i.e., we expect to see a monster bit vector.
    std::size_t total_width=boolbv_width(type);
    const auto l = parse_literal(src, unsignedbv_typet(total_width));

    const irep_idt binary =
      integer2binary(numeric_cast_v<mp_integer>(l), total_width);

    CHECK_RETURN(binary.size() == total_width);

    std::size_t offset=0;

    for(std::size_t i=0; i<components.size(); i++)
    {
      if(is_zero_width(components[i].type(), ns))
        continue;

      std::size_t component_width=boolbv_width(components[i].type());

      INVARIANT(
        offset + component_width <= total_width,
        "struct component bits shall be within struct bit vector");

      std::string component_binary=
        "#b"+id2string(binary).substr(
          total_width-offset-component_width, component_width);

      result.operands()[i]=
        parse_rec(irept(component_binary), components[i].type());

      offset+=component_width;
    }
  }

  return result;
}

exprt smt2_convt::parse_rec(const irept &src, const typet &type)
{
  if(src.get_sub().size() == 3 && src.get_sub()[0].id() == ID_let)
  {
    // This is produced by Z3
    // (let (....) (....))
    auto previous_bindings = current_bindings;
    for(const auto &binding : src.get_sub()[1].get_sub())
    {
      const irep_idt &name = binding.get_sub()[0].id();
      current_bindings.emplace(name, binding.get_sub()[1]);
    }
    exprt result = parse_rec(src.get_sub()[2], type);
    current_bindings = std::move(previous_bindings);
    return result;
  }

  auto bindings_it = current_bindings.find(src.id());
  if(bindings_it != current_bindings.end())
  {
    return parse_rec(bindings_it->second, type);
  }

  if(
    type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
    type.id() == ID_integer || type.id() == ID_rational ||
    type.id() == ID_real || type.id() == ID_c_enum ||
    type.id() == ID_c_enum_tag || type.id() == ID_fixedbv ||
    type.id() == ID_floatbv || type.id() == ID_c_bool)
  {
    return parse_literal(src, type);
  }
  else if(type.id()==ID_bool)
  {
    if(src.id()==ID_1 || src.id()==ID_true)
      return true_exprt();
    else if(src.id()==ID_0 || src.id()==ID_false)
      return false_exprt();
  }
  else if(type.id()==ID_pointer)
  {
    // these come in as bit-vector literals
    std::size_t width=boolbv_width(type);
    constant_exprt bv_expr = parse_literal(src, unsignedbv_typet(width));

    mp_integer v = numeric_cast_v<mp_integer>(bv_expr);

    // split into object and offset
    mp_integer pow=power(2, width-config.bv_encoding.object_bits);
    pointer_logict::pointert ptr{numeric_cast_v<std::size_t>(v / pow), v % pow};
    return annotated_pointer_constant_exprt(
      bv_expr.get_value(),
      pointer_logic.pointer_expr(ptr, to_pointer_type(type)));
  }
  else if(type.id()==ID_struct)
  {
    return parse_struct(src, to_struct_type(type));
  }
  else if(type.id() == ID_struct_tag)
  {
    auto struct_expr =
      parse_struct(src, ns.follow_tag(to_struct_tag_type(type)));
    // restore the tag type
    struct_expr.type() = type;
    return std::move(struct_expr);
  }
  else if(type.id()==ID_union)
  {
    return parse_union(src, to_union_type(type));
  }
  else if(type.id() == ID_union_tag)
  {
    auto union_expr = parse_union(src, ns.follow_tag(to_union_tag_type(type)));
    // restore the tag type
    union_expr.type() = type;
    return union_expr;
  }
  else if(type.id()==ID_array)
  {
    return parse_array(src, to_array_type(type));
  }

  return nil_exprt();
}

void smt2_convt::convert_address_of_rec(
  const exprt &expr,
  const pointer_typet &result_type)
{
  if(
    expr.id() == ID_symbol || expr.is_constant() ||
    expr.id() == ID_string_constant || expr.id() == ID_label)
  {
    const std::size_t object_bits = config.bv_encoding.object_bits;
    const std::size_t max_objects = std::size_t(1) << object_bits;
    const mp_integer object_id = pointer_logic.add_object(expr);

    if(object_id >= max_objects)
    {
      throw analysis_exceptiont{
        "too many addressed objects: maximum number of objects is set to 2^n=" +
        std::to_string(max_objects) +
        " (with n=" + std::to_string(object_bits) + "); " +
        "use the `--object-bits n` option to increase the maximum number"};
    }

    out << "(concat (_ bv" << object_id << " " << object_bits << ")"
        << " (_ bv0 " << boolbv_width(result_type) - object_bits << "))";
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);

    const exprt &array = index_expr.array();
    const exprt &index = index_expr.index();

    if(index.is_zero())
    {
      if(array.type().id()==ID_pointer)
        convert_expr(array);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array, result_type);
      else
        UNREACHABLE;
    }
    else
    {
      // this is really pointer arithmetic
      index_exprt new_index_expr = index_expr;
      new_index_expr.index() = from_integer(0, index.type());

      address_of_exprt address_of_expr(
        new_index_expr,
        pointer_type(to_array_type(array.type()).element_type()));

      plus_exprt plus_expr{address_of_expr, index};

      convert_expr(plus_expr);
    }
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);

    const exprt &struct_op=member_expr.struct_op();
    const typet &struct_op_type = struct_op.type();

    DATA_INVARIANT(
      struct_op_type.id() == ID_struct || struct_op_type.id() == ID_struct_tag,
      "member expression operand shall have struct type");

    const struct_typet &struct_type = to_struct_type(ns.follow(struct_op_type));

    const irep_idt &component_name = member_expr.get_component_name();

    const auto offset = member_offset(struct_type, component_name, ns);
    CHECK_RETURN(offset.has_value() && *offset >= 0);

    unsignedbv_typet index_type(boolbv_width(result_type));

    // pointer arithmetic
    out << "(bvadd ";
    convert_address_of_rec(struct_op, result_type);
    convert_expr(from_integer(*offset, index_type));
    out << ")"; // bvadd
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);

    out << "(ite ";
    convert_expr(if_expr.cond());
    out << " ";
    convert_address_of_rec(if_expr.true_case(), result_type);
    out << " ";
    convert_address_of_rec(if_expr.false_case(), result_type);
    out << ")";
  }
  else
    INVARIANT(
      false,
      "operand of address of expression should not be of kind " +
        expr.id_string());
}

static bool has_quantifier(const exprt &expr)
{
  bool result = false;
  expr.visit_post([&result](const exprt &node) {
    if(node.id() == ID_exists || node.id() == ID_forall)
      result = true;
  });
  return result;
}

literalt smt2_convt::convert(const exprt &expr)
{
  PRECONDITION(expr.is_boolean());

  // Three cases where no new handle is needed.

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);
  else if(expr.id()==ID_literal)
    return to_literal_expr(expr).get_literal();

  // Need a new handle

  out << "\n";

  exprt prepared_expr = prepare_for_convert_expr(expr);

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;

  out << "; convert\n";
  out << "; Converting var_no " << l.var_no() << " with expr ID of "
      << expr.id_string() << "\n";
  // We're converting the expression, so store it in the defined_expressions
  // store and in future we use the literal instead of the whole expression
  // Note that here we are always converting, so we do not need to consider
  // other literal kinds, only "|B###|"

  // Z3 refuses get-value when a defined symbol contains a quantifier.
  if(has_quantifier(prepared_expr))
  {
    out << "(declare-fun ";
    convert_literal(l);
    out << " () Bool)\n";
    out << "(assert (= ";
    convert_literal(l);
    out << ' ';
    convert_expr(prepared_expr);
    out << "))\n";
  }
  else
  {
    auto identifier =
      convert_identifier(std::string{"B"} + std::to_string(l.var_no()));
    defined_expressions[expr] = identifier;
    smt2_identifiers.insert(identifier);
    out << "(define-fun " << identifier << " () Bool ";
    convert_expr(prepared_expr);
    out << ")\n";
  }

  return l;
}

exprt smt2_convt::handle(const exprt &expr)
{
  // We can only improve Booleans.
  if(!expr.is_boolean())
    return expr;

  return literal_exprt(convert(expr));
}

void smt2_convt::convert_literal(const literalt l)
{
  if(l==const_literal(false))
    out << "false";
  else if(l==const_literal(true))
    out << "true";
  else
  {
    if(l.sign())
      out << "(not ";

    const auto identifier =
      convert_identifier("B" + std::to_string(l.var_no()));

    out << identifier;

    if(l.sign())
      out << ")";

    smt2_identifiers.insert(identifier);
  }
}

void smt2_convt::push()
{
  UNIMPLEMENTED;
}

void smt2_convt::push(const std::vector<exprt> &_assumptions)
{
  INVARIANT(assumptions.empty(), "nested contexts are not supported");

  assumptions = _assumptions;
}

void smt2_convt::pop()
{
  assumptions.clear();
}

static bool is_smt2_simple_identifier(const std::string &identifier)
{
  if(identifier.empty())
    return false;

  if(isdigit(identifier[0]))
    return false;

  for(auto ch : id2string(identifier))
  {
    if(!is_smt2_simple_symbol_character(ch))
      return false;
  }

  return true;
}

std::string smt2_convt::convert_identifier(const irep_idt &identifier)
{
  // Is this a "simple identifier"?
  if(is_smt2_simple_identifier(id2string(identifier)))
    return id2string(identifier);

  // Backslashes are disallowed in quoted symbols just for simplicity.
  // Otherwise, for Common Lisp compatibility they would have to be treated
  // as escaping symbols.

  std::string result = "|";

  for(auto ch : identifier)
  {
    switch(ch)
    {
    case '|':
    case '\\':
    case '&': // we use the & for escaping
      result+='&';
      result+=std::to_string(ch);
      result+=';';
      break;

    case '$': // $ _is_ allowed
    default:
      result+=ch;
    }
  }

  result += '|';

  return result;
}

std::string smt2_convt::type2id(const typet &type) const
{
  if(type.id()==ID_floatbv)
  {
    ieee_float_spect spec(to_floatbv_type(type));
    return "f"+std::to_string(spec.width())+"_"+std::to_string(spec.f);
  }
  else if(type.id() == ID_bv)
  {
    return "B" + std::to_string(to_bitvector_type(type).get_width());
  }
  else if(type.id()==ID_unsignedbv)
  {
    return "u"+std::to_string(to_unsignedbv_type(type).get_width());
  }
  else if(type.id()==ID_c_bool)
  {
    return "u"+std::to_string(to_c_bool_type(type).get_width());
  }
  else if(type.id()==ID_signedbv)
  {
    return "s"+std::to_string(to_signedbv_type(type).get_width());
  }
  else if(type.id()==ID_bool)
  {
    return "b";
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return type2id(ns.follow_tag(to_c_enum_tag_type(type)).underlying_type());
  }
  else if(type.id() == ID_pointer)
  {
    return "p" + std::to_string(to_pointer_type(type).get_width());
  }
  else if(type.id() == ID_struct_tag)
  {
    if(use_datatypes)
      return datatype_map.at(type);
    else
      return "S" + std::to_string(boolbv_width(type));
  }
  else if(type.id() == ID_union_tag)
  {
    return "U" + std::to_string(boolbv_width(type));
  }
  else if(type.id() == ID_array)
  {
    return "A" + type2id(to_array_type(type).element_type());
  }
  else
  {
    UNREACHABLE;
  }
}

std::string smt2_convt::floatbv_suffix(const exprt &expr) const
{
  PRECONDITION(!expr.operands().empty());
  return "_" + type2id(to_multi_ary_expr(expr).op0().type()) + "->" +
         type2id(expr.type());
}

void smt2_convt::convert_floatbv(const exprt &expr)
{
  PRECONDITION(!use_FPA_theory);

  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    out << convert_identifier(id);
    return;
  }

  if(expr.id()==ID_smt2_symbol)
  {
    const irep_idt &id = to_smt2_symbol(expr).get_identifier();
    out << id;
    return;
  }

  INVARIANT(
    !expr.operands().empty(), "non-symbol expressions shall have operands");

  out << '('
      << convert_identifier(
           "float_bv." + expr.id_string() + floatbv_suffix(expr));

  for(const auto &op : expr.operands())
  {
    out << ' ';
    convert_expr(op);
  }

  out << ')';
}

void smt2_convt::convert_string_literal(const std::string &s)
{
  out << '"';
  for(auto ch : s)
  {
    // " is escaped by double-quoting
    if(ch == '"')
      out << '"';
    out << ch;
  }
  out << '"';
}

void smt2_convt::convert_expr(const exprt &expr)
{
  // try hash table first
  auto converter_result = converters.find(expr.id());
  if(converter_result != converters.end())
  {
    converter_result->second(expr);
    return; // done
  }

  // huge monster case split over expression id
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "symbol must have identifier");
    out << convert_identifier(id);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id = to_nondet_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "nondet symbol must have identifier");
    out << convert_identifier("nondet_" + id2string(id));
  }
  else if(expr.id()==ID_smt2_symbol)
  {
    const irep_idt &id = to_smt2_symbol(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "smt2 symbol must have identifier");
    out << id;
  }
  else if(expr.id()==ID_typecast)
  {
    convert_typecast(to_typecast_expr(expr));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  else if(expr.id()==ID_struct)
  {
    convert_struct(to_struct_expr(expr));
  }
  else if(expr.id()==ID_union)
  {
    convert_union(to_union_expr(expr));
  }
  else if(expr.is_constant())
  {
    convert_constant(to_constant_expr(expr));
  }
  else if(expr.id() == ID_concatenation && expr.operands().size() == 1)
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      expr.type() == expr.operands().front().type(),
      "concatenation over a single operand should have matching types",
      expr.pretty());

    convert_expr(expr.operands().front());
  }
  else if(expr.id()==ID_concatenation ||
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitnand ||
          expr.id()==ID_bitnor)
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      expr.operands().size() >= 2,
      "given expression should have at least two operands",
      expr.id_string());

    out << "(";

    if(expr.id()==ID_concatenation)
      out << "concat";
    else if(expr.id()==ID_bitand)
      out << "bvand";
    else if(expr.id()==ID_bitor)
      out << "bvor";
    else if(expr.id()==ID_bitxor)
      out << "bvxor";
    else if(expr.id()==ID_bitnand)
      out << "bvnand";
    else if(expr.id()==ID_bitnor)
      out << "bvnor";

    for(const auto &op : expr.operands())
    {
      out << " ";
      flatten2bv(op);
    }

    out << ")";
  }
  else if(expr.id()==ID_bitnot)
  {
    const bitnot_exprt &bitnot_expr = to_bitnot_expr(expr);

    out << "(bvnot ";
    convert_expr(bitnot_expr.op());
    out << ")";
  }
  else if(expr.id()==ID_unary_minus)
  {
    const unary_minus_exprt &unary_minus_expr = to_unary_minus_expr(expr);

    if(
      unary_minus_expr.type().id() == ID_rational ||
      unary_minus_expr.type().id() == ID_integer ||
      unary_minus_expr.type().id() == ID_real)
    {
      out << "(- ";
      convert_expr(unary_minus_expr.op());
      out << ")";
    }
    else if(unary_minus_expr.type().id() == ID_floatbv)
    {
      // this has no rounding mode
      if(use_FPA_theory)
      {
        out << "(fp.neg ";
        convert_expr(unary_minus_expr.op());
        out << ")";
      }
      else
        convert_floatbv(unary_minus_expr);
    }
    else
    {
      out << "(bvneg ";
      convert_expr(unary_minus_expr.op());
      out << ")";
    }
  }
  else if(expr.id()==ID_unary_plus)
  {
    // A no-op (apart from type promotion)
    convert_expr(to_unary_plus_expr(expr).op());
  }
  else if(expr.id()==ID_sign)
  {
    const sign_exprt &sign_expr = to_sign_expr(expr);

    const typet &op_type = sign_expr.op().type();

    if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isNegative ";
        convert_expr(sign_expr.op());
        out << ")";
      }
      else
        convert_floatbv(sign_expr);
    }
    else if(op_type.id()==ID_signedbv)
    {
      std::size_t op_width=to_signedbv_type(op_type).get_width();

      out << "(bvslt ";
      convert_expr(sign_expr.op());
      out << " (_ bv0 " << op_width << "))";
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "sign should not be applied to unsupported type",
        sign_expr.type().id_string());
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);

    out << "(ite ";
    convert_expr(if_expr.cond());
    out << " ";
    convert_expr(if_expr.true_case());
    out << " ";
    convert_expr(if_expr.false_case());
    out << ")";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.is_boolean(),
      "logical and, or, and xor expressions should have Boolean type");
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions should have at least two operands");

    out << "(" << expr.id();
    for(const auto &op : expr.operands())
    {
      out << " ";
      convert_expr(op);
    }
    out << ")";
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);

    DATA_INVARIANT(
      implies_expr.is_boolean(), "implies expression should have Boolean type");

    out << "(=> ";
    convert_expr(implies_expr.op0());
    out << " ";
    convert_expr(implies_expr.op1());
    out << ")";
  }
  else if(expr.id()==ID_not)
  {
    const not_exprt &not_expr = to_not_expr(expr);

    DATA_INVARIANT(
      not_expr.is_boolean(), "not expression should have Boolean type");

    out << "(not ";
    convert_expr(not_expr.op());
    out << ")";
  }
  else if(expr.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(expr);

    DATA_INVARIANT(
      equal_expr.op0().type() == equal_expr.op1().type(),
      "operands of equal expression shall have same type");

    if(is_zero_width(equal_expr.lhs().type(), ns))
    {
      convert_expr(true_exprt());
    }
    else
    {
      out << "(= ";
      convert_expr(equal_expr.op0());
      out << " ";
      convert_expr(equal_expr.op1());
      out << ")";
    }
  }
  else if(expr.id() == ID_notequal)
  {
    const notequal_exprt &notequal_expr = to_notequal_expr(expr);

    DATA_INVARIANT(
      notequal_expr.op0().type() == notequal_expr.op1().type(),
      "operands of not equal expression shall have same type");

    out << "(not (= ";
    convert_expr(notequal_expr.op0());
    out << " ";
    convert_expr(notequal_expr.op1());
    out << "))";
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    // These are not the same as (= A B)
    // because of NaN and negative zero.
    const auto &rel_expr = to_binary_relation_expr(expr);

    DATA_INVARIANT(
      rel_expr.lhs().type() == rel_expr.rhs().type(),
      "operands of float equal and not equal expressions shall have same type");

    // The FPA theory properly treats NaN and negative zero.
    if(use_FPA_theory)
    {
      if(rel_expr.id() == ID_ieee_float_notequal)
        out << "(not ";

      out << "(fp.eq ";
      convert_expr(rel_expr.lhs());
      out << " ";
      convert_expr(rel_expr.rhs());
      out << ")";

      if(rel_expr.id() == ID_ieee_float_notequal)
        out << ")";
    }
    else
      convert_floatbv(expr);
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    convert_relation(to_binary_relation_expr(expr));
  }
  else if(expr.id()==ID_plus)
  {
    convert_plus(to_plus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_plus)
  {
    convert_floatbv_plus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_minus)
  {
    convert_minus(to_minus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_minus)
  {
    convert_floatbv_minus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_div)
  {
    convert_div(to_div_expr(expr));
  }
  else if(expr.id()==ID_floatbv_div)
  {
    convert_floatbv_div(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_mod)
  {
    convert_mod(to_mod_expr(expr));
  }
  else if(expr.id() == ID_euclidean_mod)
  {
    convert_euclidean_mod(to_euclidean_mod_expr(expr));
  }
  else if(expr.id()==ID_mult)
  {
    convert_mult(to_mult_expr(expr));
  }
  else if(expr.id()==ID_floatbv_mult)
  {
    convert_floatbv_mult(to_ieee_float_op_expr(expr));
  }
  else if(expr.id() == ID_floatbv_rem)
  {
    convert_floatbv_rem(to_binary_expr(expr));
  }
  else if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr = to_address_of_expr(expr);
    convert_address_of_rec(
      address_of_expr.object(), to_pointer_type(address_of_expr.type()));
  }
  else if(expr.id() == ID_array_of)
  {
    const auto &array_of_expr = to_array_of_expr(expr);

    DATA_INVARIANT(
      array_of_expr.type().id() == ID_array,
      "array of expression shall have array type");

    if(use_as_const)
    {
      out << "((as const ";
      convert_type(array_of_expr.type());
      out << ") ";
      convert_expr(array_of_expr.what());
      out << ")";
    }
    else
    {
      defined_expressionst::const_iterator it =
        defined_expressions.find(array_of_expr);
      CHECK_RETURN(it != defined_expressions.end());
      out << it->second;
    }
  }
  else if(expr.id() == ID_array_comprehension)
  {
    const auto &array_comprehension = to_array_comprehension_expr(expr);

    DATA_INVARIANT(
      array_comprehension.type().id() == ID_array,
      "array_comprehension expression shall have array type");

    if(use_lambda_for_array)
    {
      out << "(lambda ((";
      convert_expr(array_comprehension.arg());
      out << " ";
      convert_type(array_comprehension.type().size().type());
      out << ")) ";
      convert_expr(array_comprehension.body());
      out << ")";
    }
    else
    {
      const auto &it = defined_expressions.find(array_comprehension);
      CHECK_RETURN(it != defined_expressions.end());
      out << it->second;
    }
  }
  else if(expr.id()==ID_index)
  {
    convert_index(to_index_expr(expr));
  }
  else if(expr.id()==ID_ashr ||
          expr.id()==ID_lshr ||
          expr.id()==ID_shl)
  {
    const shift_exprt &shift_expr = to_shift_expr(expr);
    const typet &type = shift_expr.type();

    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv)
    {
      if(shift_expr.id() == ID_ashr)
        out << "(bvashr ";
      else if(shift_expr.id() == ID_lshr)
        out << "(bvlshr ";
      else if(shift_expr.id() == ID_shl)
        out << "(bvshl ";
      else
        UNREACHABLE;

      convert_expr(shift_expr.op());
      out << " ";

      // SMT2 requires the shift distance to have the same width as
      // the value that is shifted -- odd!

      if(shift_expr.distance().type().id() == ID_integer)
      {
        const mp_integer i =
          numeric_cast_v<mp_integer>(to_constant_expr(shift_expr.distance()));

        // shift distance must be bit vector
        std::size_t width_op0 = boolbv_width(shift_expr.op().type());
        exprt tmp=from_integer(i, unsignedbv_typet(width_op0));
        convert_expr(tmp);
      }
      else if(
        shift_expr.distance().type().id() == ID_signedbv ||
        shift_expr.distance().type().id() == ID_unsignedbv ||
        shift_expr.distance().type().id() == ID_c_enum ||
        shift_expr.distance().type().id() == ID_c_bool)
      {
        std::size_t width_op0 = boolbv_width(shift_expr.op().type());
        std::size_t width_op1 = boolbv_width(shift_expr.distance().type());

        if(width_op0==width_op1)
          convert_expr(shift_expr.distance());
        else if(width_op0>width_op1)
        {
          out << "((_ zero_extend " << width_op0-width_op1 << ") ";
          convert_expr(shift_expr.distance());
          out << ")"; // zero_extend
        }
        else // width_op0<width_op1
        {
          out << "((_ extract " << width_op0-1 << " 0) ";
          convert_expr(shift_expr.distance());
          out << ")"; // extract
        }
      }
      else
        UNEXPECTEDCASE(
          "unsupported distance type for " + shift_expr.id_string() + ": " +
          type.id_string());

      out << ")"; // bv*sh
    }
    else
      UNEXPECTEDCASE(
        "unsupported type for " + shift_expr.id_string() + ": " +
        type.id_string());
  }
  else if(expr.id() == ID_rol || expr.id() == ID_ror)
  {
    const shift_exprt &shift_expr = to_shift_expr(expr);
    const typet &type = shift_expr.type();

    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_bv)
    {
      // SMT-LIB offers rotate_left and rotate_right, but these require a
      // constant distance.
      if(shift_expr.id() == ID_rol)
        out << "((_ rotate_left";
      else if(shift_expr.id() == ID_ror)
        out << "((_ rotate_right";
      else
        UNREACHABLE;

      out << ' ';

      auto distance_int_op = numeric_cast<mp_integer>(shift_expr.distance());

      if(distance_int_op.has_value())
      {
        out << distance_int_op.value();
      }
      else
        UNEXPECTEDCASE(
          "distance type for " + shift_expr.id_string() + "must be constant");

      out << ") ";
      convert_expr(shift_expr.op());

      out << ")"; // rotate_*
    }
    else
      UNEXPECTEDCASE(
        "unsupported type for " + shift_expr.id_string() + ": " +
        type.id_string());
  }
  else if(expr.id() == ID_named_term)
  {
    const auto &named_term_expr = to_named_term_expr(expr);
    out << "(! ";
    convert(named_term_expr.value());
    out << " :named "
        << convert_identifier(named_term_expr.symbol().get_identifier()) << ')';
  }
  else if(expr.id()==ID_with)
  {
    convert_with(to_with_expr(expr));
  }
  else if(expr.id()==ID_update)
  {
    convert_update(to_update_expr(expr));
  }
  else if(expr.id() == ID_object_address)
  {
    out << "(object-address ";
    convert_string_literal(
      id2string(to_object_address_expr(expr).object_identifier()));
    out << ')';
  }
  else if(expr.id() == ID_element_address)
  {
    // We turn this binary expression into a ternary expression
    // by adding the size of the array elements as third argument.
    const auto &element_address_expr = to_element_address_expr(expr);

    auto element_size_expr_opt =
      ::size_of_expr(element_address_expr.element_type(), ns);
    CHECK_RETURN(element_size_expr_opt.has_value());

    out << "(element-address-" << type2id(expr.type()) << ' ';
    convert_expr(element_address_expr.base());
    out << ' ';
    convert_expr(element_address_expr.index());
    out << ' ';
    convert_expr(typecast_exprt::conditional_cast(
      *element_size_expr_opt, element_address_expr.index().type()));
    out << ')';
  }
  else if(expr.id() == ID_field_address)
  {
    const auto &field_address_expr = to_field_address_expr(expr);
    out << "(field-address-" << type2id(expr.type()) << ' ';
    convert_expr(field_address_expr.base());
    out << ' ';
    convert_string_literal(id2string(field_address_expr.component_name()));
    out << ')';
  }
  else if(expr.id()==ID_member)
  {
    convert_member(to_member_expr(expr));
  }
  else if(expr.id()==ID_pointer_offset)
  {
    const auto &op = to_pointer_offset_expr(expr).pointer();

    DATA_INVARIANT(
      op.type().id() == ID_pointer,
      "operand of pointer offset expression shall be of pointer type");

    std::size_t offset_bits =
      boolbv_width(op.type()) - config.bv_encoding.object_bits;
    std::size_t result_width=boolbv_width(expr.type());

    // max extract width
    if(offset_bits>result_width)
      offset_bits=result_width;

    // too few bits?
    if(result_width>offset_bits)
      out << "((_ zero_extend " << result_width-offset_bits << ") ";

    out << "((_ extract " << offset_bits-1 << " 0) ";
    convert_expr(op);
    out << ")";

    if(result_width>offset_bits)
      out << ")"; // zero_extend
  }
  else if(expr.id()==ID_pointer_object)
  {
    const auto &op = to_pointer_object_expr(expr).pointer();

    DATA_INVARIANT(
      op.type().id() == ID_pointer,
      "pointer object expressions should be of pointer type");

    std::size_t ext=boolbv_width(expr.type())-config.bv_encoding.object_bits;
    std::size_t pointer_width = boolbv_width(op.type());

    if(ext>0)
      out << "((_ zero_extend " << ext << ") ";

    out << "((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(op);
    out << ")";

    if(ext>0)
      out << ")"; // zero_extend
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    convert_is_dynamic_object(to_unary_expr(expr));
  }
  else if(expr.id() == ID_is_invalid_pointer)
  {
    const auto &op = to_unary_expr(expr).op();
    std::size_t pointer_width = boolbv_width(op.type());
    out << "(= ((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(op);
    out << ") (_ bv" << pointer_logic.get_invalid_object()
        << " " << config.bv_encoding.object_bits << "))";
  }
  else if(expr.id()==ID_string_constant)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    out << it->second;
  }
  else if(expr.id()==ID_extractbit)
  {
    const extractbit_exprt &extractbit_expr = to_extractbit_expr(expr);

    if(extractbit_expr.index().is_constant())
    {
      const mp_integer i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbit_expr.index()));

      out << "(= ((_ extract " << i << " " << i << ") ";
      flatten2bv(extractbit_expr.src());
      out << ") #b1)";
    }
    else
    {
      out << "(= ((_ extract 0 0) ";
      // the arguments of the shift need to have the same width
      out << "(bvlshr ";
      flatten2bv(extractbit_expr.src());
      typecast_exprt tmp(extractbit_expr.index(), extractbit_expr.src().type());
      convert_expr(tmp);
      out << ")) bin1)"; // bvlshr, extract, =
    }
  }
  else if(expr.id()==ID_extractbits)
  {
    const extractbits_exprt &extractbits_expr = to_extractbits_expr(expr);

    if(
      extractbits_expr.upper().is_constant() &&
      extractbits_expr.lower().is_constant())
    {
      mp_integer op1_i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbits_expr.upper()));
      mp_integer op2_i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbits_expr.lower()));

      if(op2_i>op1_i)
        std::swap(op1_i, op2_i);

      // now op1_i>=op2_i

      out << "((_ extract " << op1_i << " " << op2_i << ") ";
      flatten2bv(extractbits_expr.src());
      out << ")";
    }
    else
    {
      #if 0
      out << "(= ((_ extract 0 0) ";
      // the arguments of the shift need to have the same width
      out << "(bvlshr ";
      convert_expr(expr.op0());
      typecast_exprt tmp(expr.op0().type());
      tmp.op0()=expr.op1();
      convert_expr(tmp);
      out << ")) bin1)"; // bvlshr, extract, =
      #endif
      SMT2_TODO("smt2: extractbits with non-constant index");
    }
  }
  else if(expr.id()==ID_replication)
  {
    const replication_exprt &replication_expr = to_replication_expr(expr);

    mp_integer times = numeric_cast_v<mp_integer>(replication_expr.times());

    out << "((_ repeat " << times << ") ";
    flatten2bv(replication_expr.op());
    out << ")";
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    INVARIANT(
      false, "byte_extract ops should be lowered in prepare_for_convert_expr");
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    INVARIANT(
      false, "byte_update ops should be lowered in prepare_for_convert_expr");
  }
  else if(expr.id()==ID_abs)
  {
    const abs_exprt &abs_expr = to_abs_expr(expr);

    const typet &type = abs_expr.type();

    if(type.id()==ID_signedbv)
    {
      std::size_t result_width = to_signedbv_type(type).get_width();

      out << "(ite (bvslt ";
      convert_expr(abs_expr.op());
      out << " (_ bv0 " << result_width << ")) ";
      out << "(bvneg ";
      convert_expr(abs_expr.op());
      out << ") ";
      convert_expr(abs_expr.op());
      out << ")";
    }
    else if(type.id()==ID_fixedbv)
    {
      std::size_t result_width=to_fixedbv_type(type).get_width();

      out << "(ite (bvslt ";
      convert_expr(abs_expr.op());
      out << " (_ bv0 " << result_width << ")) ";
      out << "(bvneg ";
      convert_expr(abs_expr.op());
      out << ") ";
      convert_expr(abs_expr.op());
      out << ")";
    }
    else if(type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.abs ";
        convert_expr(abs_expr.op());
        out << ")";
      }
      else
        convert_floatbv(abs_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnan)
  {
    const isnan_exprt &isnan_expr = to_isnan_expr(expr);

    const typet &op_type = isnan_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isNaN ";
        convert_expr(isnan_expr.op());
        out << ")";
      }
      else
        convert_floatbv(isnan_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isfinite)
  {
    const isfinite_exprt &isfinite_expr = to_isfinite_expr(expr);

    const typet &op_type = isfinite_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(and ";

        out << "(not (fp.isNaN ";
        convert_expr(isfinite_expr.op());
        out << "))";

        out << "(not (fp.isInfinite ";
        convert_expr(isfinite_expr.op());
        out << "))";

        out << ")";
      }
      else
        convert_floatbv(isfinite_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isinf)
  {
    const isinf_exprt &isinf_expr = to_isinf_expr(expr);

    const typet &op_type = isinf_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isInfinite ";
        convert_expr(isinf_expr.op());
        out << ")";
      }
      else
        convert_floatbv(isinf_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnormal)
  {
    const isnormal_exprt &isnormal_expr = to_isnormal_expr(expr);

    const typet &op_type = isnormal_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isNormal ";
        convert_expr(isnormal_expr.op());
        out << ")";
      }
      else
        convert_floatbv(isnormal_expr);
    }
    else
      UNREACHABLE;
  }
  else if(
    can_cast_expr<plus_overflow_exprt>(expr) ||
    can_cast_expr<minus_overflow_exprt>(expr) ||
    expr.id() == ID_overflow_result_plus ||
    expr.id() == ID_overflow_result_minus)
  {
    const bool keep_result = can_cast_expr<overflow_result_exprt>(expr);

    const auto &op0 = to_binary_expr(expr).op0();
    const auto &op1 = to_binary_expr(expr).op1();

    DATA_INVARIANT(
      keep_result || expr.is_boolean(),
      "overflow plus and overflow minus expressions shall be of Boolean type");

    bool subtract = can_cast_expr<minus_overflow_exprt>(expr) ||
                    expr.id() == ID_overflow_result_minus;
    const typet &op_type = op0.type();
    std::size_t width=boolbv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      // an overflow occurs if the top two bits of the extended sum differ
      out << "(let ((?sum (";
      out << (subtract?"bvsub":"bvadd");
      out << " ((_ sign_extend 1) ";
      convert_expr(op0);
      out << ")";
      out << " ((_ sign_extend 1) ";
      convert_expr(op1);
      out << ")))) "; // sign_extend, bvadd/sub
      if(keep_result)
      {
        if(use_datatypes)
        {
          const std::string &smt_typename = datatype_map.at(expr.type());

          // use the constructor for the Z3 datatype
          out << "(mk-" << smt_typename;
        }
        else
          out << "(concat";

        out << " ((_ extract " << width - 1 << " 0) ?sum) ";
        if(!use_datatypes)
          out << "(ite ";
      }
      out << "(not (= "
                   "((_ extract " << width << " " << width << ") ?sum) "
                   "((_ extract " << (width-1) << " " << (width-1) << ") ?sum)";
      out << "))"; // =, not
      if(keep_result)
      {
        if(!use_datatypes)
          out << " #b1 #b0)";
        out << ")"; // concat
      }
      out << ")"; // let
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_pointer)
    {
      // overflow is simply carry-out
      out << "(let ((?sum (" << (subtract ? "bvsub" : "bvadd");
      out << " ((_ zero_extend 1) ";
      convert_expr(op0);
      out << ")";
      out << " ((_ zero_extend 1) ";
      convert_expr(op1);
      out << "))))"; // zero_extend, bvsub/bvadd
      if(keep_result && !use_datatypes)
        out << " ?sum";
      else
      {
        if(keep_result && use_datatypes)
        {
          const std::string &smt_typename = datatype_map.at(expr.type());

          // use the constructor for the Z3 datatype
          out << "(mk-" << smt_typename;
          out << " ((_ extract " << width - 1 << " 0) ?sum) ";
        }

        out << "(= ";
        out << "((_ extract " << width << " " << width << ") ?sum)";
        out << "#b1)"; // =

        if(keep_result && use_datatypes)
          out << ")"; // mk
      }
      out << ")"; // let
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "overflow check should not be performed on unsupported type",
        op_type.id_string());
  }
  else if(
    can_cast_expr<mult_overflow_exprt>(expr) ||
    expr.id() == ID_overflow_result_mult)
  {
    const bool keep_result = can_cast_expr<overflow_result_exprt>(expr);

    const auto &op0 = to_binary_expr(expr).op0();
    const auto &op1 = to_binary_expr(expr).op1();

    DATA_INVARIANT(
      keep_result || expr.is_boolean(),
      "overflow mult expression shall be of Boolean type");

    // No better idea than to multiply with double the bits and then compare
    // with max value.

    const typet &op_type = op0.type();
    std::size_t width=boolbv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      out << "(let ( (prod (bvmul ((_ sign_extend " << width << ") ";
      convert_expr(op0);
      out << ") ((_ sign_extend " << width << ") ";
      convert_expr(op1);
      out << ")) )) ";
      if(keep_result)
      {
        if(use_datatypes)
        {
          const std::string &smt_typename = datatype_map.at(expr.type());

          // use the constructor for the Z3 datatype
          out << "(mk-" << smt_typename;
        }
        else
          out << "(concat";

        out << " ((_ extract " << width - 1 << " 0) prod) ";
        if(!use_datatypes)
          out << "(ite ";
      }
      out << "(or (bvsge prod (_ bv" << power(2, width-1) << " "
          << width*2 << "))";
      out << " (bvslt prod (bvneg (_ bv" << power(2, width - 1) << " "
          << width * 2 << "))))";
      if(keep_result)
      {
        if(!use_datatypes)
          out << " #b1 #b0)";
        out << ")"; // concat
      }
      out << ")";
    }
    else if(op_type.id()==ID_unsignedbv)
    {
      out << "(let ((prod (bvmul ((_ zero_extend " << width << ") ";
      convert_expr(op0);
      out << ") ((_ zero_extend " << width << ") ";
      convert_expr(op1);
      out << ")))) ";
      if(keep_result)
      {
        if(use_datatypes)
        {
          const std::string &smt_typename = datatype_map.at(expr.type());

          // use the constructor for the Z3 datatype
          out << "(mk-" << smt_typename;
        }
        else
          out << "(concat";

        out << " ((_ extract " << width - 1 << " 0) prod) ";
        if(!use_datatypes)
          out << "(ite ";
      }
      out << "(bvuge prod (_ bv" << power(2, width) << " " << width * 2 << "))";
      if(keep_result)
      {
        if(!use_datatypes)
          out << " #b1 #b0)";
        out << ")"; // concat
      }
      out << ")";
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "overflow check should not be performed on unsupported type",
        op_type.id_string());
  }
  else if(expr.id() == ID_saturating_plus || expr.id() == ID_saturating_minus)
  {
    const bool subtract = expr.id() == ID_saturating_minus;
    const auto &op_type = expr.type();
    const auto &op0 = to_binary_expr(expr).op0();
    const auto &op1 = to_binary_expr(expr).op1();

    if(op_type.id() == ID_signedbv)
    {
      auto width = to_signedbv_type(op_type).get_width();

      // compute sum with one extra bit
      out << "(let ((?sum (";
      out << (subtract ? "bvsub" : "bvadd");
      out << " ((_ sign_extend 1) ";
      convert_expr(op0);
      out << ")";
      out << " ((_ sign_extend 1) ";
      convert_expr(op1);
      out << ")))) "; // sign_extend, bvadd/sub

      // pick one of MAX, MIN, or the sum
      out << "(ite (= "
             "((_ extract "
          << width << " " << width
          << ") ?sum) "
             "((_ extract "
          << (width - 1) << " " << (width - 1) << ") ?sum)";
      out << ") "; // =

      // no overflow and no underflow case, return the sum
      out << "((_ extract " << width - 1 << " 0) ?sum) ";

      // MAX
      out << "(ite (= ((_ extract " << width << " " << width << ") ?sum) #b0) ";
      convert_expr(to_signedbv_type(op_type).largest_expr());

      // MIN
      convert_expr(to_signedbv_type(op_type).smallest_expr());
      out << ")))"; // ite, ite, let
    }
    else if(op_type.id() == ID_unsignedbv)
    {
      auto width = to_unsignedbv_type(op_type).get_width();

      // compute sum with one extra bit
      out << "(let ((?sum (" << (subtract ? "bvsub" : "bvadd");
      out << " ((_ zero_extend 1) ";
      convert_expr(op0);
      out << ")";
      out << " ((_ zero_extend 1) ";
      convert_expr(op1);
      out << "))))"; // zero_extend, bvsub/bvadd

      // pick one of MAX, MIN, or the sum
      out << "(ite (= ((_ extract " << width << " " << width << ") ?sum) #b0) ";

      // no overflow and no underflow case, return the sum
      out << " ((_ extract " << width - 1 << " 0) ?sum) ";

      // overflow when adding, underflow when subtracting
      if(subtract)
        convert_expr(to_unsignedbv_type(op_type).smallest_expr());
      else
        convert_expr(to_unsignedbv_type(op_type).largest_expr());

      // MIN
      out << "))"; // ite, let
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "saturating_plus/minus on unsupported type",
        op_type.id_string());
  }
  else if(expr.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    out << it->second;
  }
  else if(expr.id()==ID_literal)
  {
    convert_literal(to_literal_expr(expr).get_literal());
  }
  else if(expr.id()==ID_forall ||
          expr.id()==ID_exists)
  {
    const quantifier_exprt &quantifier_expr = to_quantifier_expr(expr);

    if(solver==solvert::MATHSAT)
      // NOLINTNEXTLINE(readability/throw)
      throw "MathSAT does not support quantifiers";

    if(quantifier_expr.id() == ID_forall)
      out << "(forall ";
    else if(quantifier_expr.id() == ID_exists)
      out << "(exists ";

    out << '(';
    bool first = true;
    for(const auto &bound : quantifier_expr.variables())
    {
      if(first)
        first = false;
      else
        out << ' ';
      out << '(';
      convert_expr(bound);
      out << ' ';
      convert_type(bound.type());
      out << ')';
    }
    out << ") ";

    convert_expr(quantifier_expr.where());

    out << ')';
  }
  else if(
    const auto object_size = expr_try_dynamic_cast<object_size_exprt>(expr))
  {
    out << object_sizes[*object_size];
  }
  else if(expr.id()==ID_let)
  {
    const let_exprt &let_expr=to_let_expr(expr);
    const auto &variables = let_expr.variables();
    const auto &values = let_expr.values();

    out << "(let (";
    bool first = true;

    for(auto &binding : make_range(variables).zip(values))
    {
      if(first)
        first = false;
      else
        out << ' ';

      out << '(';
      convert_expr(binding.first);
      out << ' ';
      convert_expr(binding.second);
      out << ')';
    }

    out << ") "; // bindings

    convert_expr(let_expr.where());
    out << ')'; // let
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    UNEXPECTEDCASE(
      "smt2_convt::convert_expr: '" + expr.id_string() +
      "' is not yet supported");
  }
  else if(expr.id() == ID_bswap)
  {
    const bswap_exprt &bswap_expr = to_bswap_expr(expr);

    DATA_INVARIANT(
      bswap_expr.op().type() == bswap_expr.type(),
      "operand of byte swap expression shall have same type as the expression");

    // first 'let' the operand
    out << "(let ((bswap_op ";
    convert_expr(bswap_expr.op());
    out << ")) ";

    if(
      bswap_expr.type().id() == ID_signedbv ||
      bswap_expr.type().id() == ID_unsignedbv)
    {
      const std::size_t width =
        to_bitvector_type(bswap_expr.type()).get_width();

      const std::size_t bits_per_byte = bswap_expr.get_bits_per_byte();

      // width must be multiple of bytes
      DATA_INVARIANT(
        width % bits_per_byte == 0,
        "bit width indicated by type of bswap expression should be a multiple "
        "of the number of bits per byte");

      const std::size_t bytes = width / bits_per_byte;

      if(bytes <= 1)
        out << "bswap_op";
      else
      {
        // do a parallel 'let' for each byte
        out << "(let (";

        for(std::size_t byte = 0; byte < bytes; byte++)
        {
          if(byte != 0)
            out << ' ';
          out << "(bswap_byte_" << byte << ' ';
          out << "((_ extract " << (byte * bits_per_byte + (bits_per_byte - 1))
              << " " << (byte * bits_per_byte) << ") bswap_op)";
          out << ')';
        }

        out << ") ";

        // now stitch back together with 'concat'
        out << "(concat";

        for(std::size_t byte = 0; byte < bytes; byte++)
          out << " bswap_byte_" << byte;

        out << ')'; // concat
        out << ')'; // let bswap_byte_*
      }
    }
    else
      UNEXPECTEDCASE("bswap must get bitvector operand");

    out << ')'; // let bswap_op
  }
  else if(expr.id() == ID_popcount)
  {
    convert_expr(simplify_expr(to_popcount_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_count_leading_zeros)
  {
    convert_expr(simplify_expr(to_count_leading_zeros_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_count_trailing_zeros)
  {
    convert_expr(simplify_expr(to_count_trailing_zeros_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_find_first_set)
  {
    convert_expr(simplify_expr(to_find_first_set_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_bitreverse)
  {
    convert_expr(simplify_expr(to_bitreverse_expr(expr).lower(), ns));
  }
  else if(expr.id() == ID_function_application)
  {
    const auto &function_application_expr = to_function_application_expr(expr);
    // do not use parentheses if there function is a constant
    if(function_application_expr.arguments().empty())
    {
      convert_expr(function_application_expr.function());
    }
    else
    {
      out << '(';
      convert_expr(function_application_expr.function());
      for(auto &op : function_application_expr.arguments())
      {
        out << ' ';
        convert_expr(op);
      }
      out << ')';
    }
  }
  else
    INVARIANT_WITH_DIAGNOSTICS(
      false,
      "smt2_convt::convert_expr should not be applied to unsupported type",
      expr.id_string());
}

void smt2_convt::convert_typecast(const typecast_exprt &expr)
{
  const exprt &src = expr.op();

  typet dest_type = expr.type();
  if(dest_type.id()==ID_c_enum_tag)
    dest_type=ns.follow_tag(to_c_enum_tag_type(dest_type));

  typet src_type = src.type();
  if(src_type.id()==ID_c_enum_tag)
    src_type=ns.follow_tag(to_c_enum_tag_type(src_type));

  if(dest_type.id()==ID_bool)
  {
    // this is comparison with zero
    if(src_type.id()==ID_signedbv ||
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_fixedbv ||
       src_type.id()==ID_pointer ||
       src_type.id()==ID_integer)
    {
      out << "(not (= ";
      convert_expr(src);
      out << " ";
      convert_expr(from_integer(0, src_type));
      out << "))";
    }
    else if(src_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(not (fp.isZero ";
        convert_expr(src);
        out << "))";
      }
      else
        convert_floatbv(expr);
    }
    else
    {
      UNEXPECTEDCASE("TODO typecast1 "+src_type.id_string()+" -> bool");
    }
  }
  else if(dest_type.id()==ID_c_bool)
  {
    std::size_t to_width=boolbv_width(dest_type);
    out << "(ite ";
    out << "(not (= ";
    convert_expr(src);
    out << " ";
    convert_expr(from_integer(0, src_type));
    out << "))"; // not, =
    out << " (_ bv1 " << to_width << ")";
    out << " (_ bv0 " << to_width << ")";
    out << ")"; // ite
  }
  else if(dest_type.id()==ID_signedbv ||
          dest_type.id()==ID_unsignedbv ||
          dest_type.id()==ID_c_enum ||
          dest_type.id()==ID_bv)
  {
    std::size_t to_width=boolbv_width(dest_type);

    if(src_type.id()==ID_signedbv || // from signedbv
       src_type.id()==ID_unsignedbv || // from unsigedbv
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_c_enum ||
       src_type.id()==ID_bv)
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        convert_expr(src); // ignore
      else if(from_width<to_width) // extend
      {
        if(src_type.id()==ID_signedbv)
          out << "((_ sign_extend ";
        else
          out << "((_ zero_extend ";

        out << (to_width-from_width)
            << ") "; // ind
        convert_expr(src);
        out << ")";
      }
      else // chop off extra bits
      {
        out << "((_ extract " << (to_width-1) << " 0) ";
        convert_expr(src);
        out << ")";
      }
    }
    else if(src_type.id()==ID_fixedbv) // from fixedbv to int
    {
      const fixedbv_typet &fixedbv_type=to_fixedbv_type(src_type);

      std::size_t from_width=fixedbv_type.get_width();
      std::size_t from_integer_bits=fixedbv_type.get_integer_bits();
      std::size_t from_fraction_bits=fixedbv_type.get_fraction_bits();

      // we might need to round up in case of negative numbers
      // e.g., (int)(-1.00001)==1

      out << "(let ((?tcop ";
      convert_expr(src);
      out << ")) ";

      out << "(bvadd ";

      if(to_width>from_integer_bits)
      {
        out << "((_ sign_extend "
            << (to_width-from_integer_bits) << ") ";
        out << "((_ extract " << (from_width-1) << " "
            << from_fraction_bits << ") ";
        convert_expr(src);
        out << "))";
      }
      else
      {
        out << "((_ extract " << (from_fraction_bits+to_width-1)
            << " " << from_fraction_bits << ") ";
        convert_expr(src);
        out << ")";
      }

      out << " (ite (and ";

      // some fraction bit is not zero
      out << "(not (= ((_ extract " << (from_fraction_bits-1) << " 0) ?tcop) "
             "(_ bv0 " << from_fraction_bits << ")))";

      // number negative
      out << " (= ((_ extract " << (from_width-1) << " " << (from_width-1)
          << ") ?tcop) #b1)";

      out << ")"; // and

      out << " (_ bv1 " << to_width << ") (_ bv0 " << to_width << "))"; // ite
      out << ")"; // bvadd
      out << ")"; // let
    }
    else if(src_type.id()==ID_floatbv) // from floatbv to int
    {
      if(dest_type.id()==ID_bv)
      {
        // this is _NOT_ a semantic conversion, but bit-wise

        if(use_FPA_theory)
        {
          defined_expressionst::const_iterator it =
            defined_expressions.find(expr);
          CHECK_RETURN(it != defined_expressions.end());
          out << it->second;
        }
        else
        {
          // straight-forward if width matches
          convert_expr(src);
        }
      }
      else if(dest_type.id()==ID_signedbv)
      {
        // this should be floatbv_typecast, not typecast
        UNEXPECTEDCASE(
          "typecast unexpected "+src_type.id_string()+" -> "+
          dest_type.id_string());
      }
      else if(dest_type.id()==ID_unsignedbv)
      {
        // this should be floatbv_typecast, not typecast
        UNEXPECTEDCASE(
          "typecast unexpected "+src_type.id_string()+" -> "+
          dest_type.id_string());
      }
    }
    else if(src_type.id()==ID_bool) // from boolean to int
    {
      out << "(ite ";
      convert_expr(src);

      if(dest_type.id()==ID_fixedbv)
      {
        fixedbv_spect spec(to_fixedbv_type(dest_type));
        out << " (concat (_ bv1 "
            << spec.integer_bits << ") " <<
               "(_ bv0 " << spec.get_fraction_bits() << ")) " <<
               "(_ bv0 " << spec.width << ")";
      }
      else
      {
        out << " (_ bv1 " << to_width << ")";
        out << " (_ bv0 " << to_width << ")";
      }

      out << ")";
    }
    else if(src_type.id()==ID_pointer) // from pointer to int
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width<to_width) // extend
      {
        out << "((_ sign_extend ";
        out << (to_width-from_width)
            << ") ";
        convert_expr(src);
        out << ")";
      }
      else // chop off extra bits
      {
        out << "((_ extract " << (to_width-1) << " 0) ";
        convert_expr(src);
        out << ")";
      }
    }
    else if(src_type.id()==ID_integer) // from integer to bit-vector
    {
      // must be constant
      if(src.is_constant())
      {
        mp_integer i = numeric_cast_v<mp_integer>(to_constant_expr(src));
        out << "(_ bv" << i << " " << to_width << ")";
      }
      else
        SMT2_TODO("can't convert non-constant integer to bitvector");
    }
    else if(
      src_type.id() == ID_struct ||
      src_type.id() == ID_struct_tag) // flatten a struct to a bit-vector
    {
      if(use_datatypes)
      {
        INVARIANT(
          boolbv_width(src_type) == boolbv_width(dest_type),
          "bit vector with of source and destination type shall be equal");
        flatten2bv(src);
      }
      else
      {
        INVARIANT(
          boolbv_width(src_type) == boolbv_width(dest_type),
          "bit vector with of source and destination type shall be equal");
        convert_expr(src); // nothing else to do!
      }
    }
    else if(
      src_type.id() == ID_union ||
      src_type.id() == ID_union_tag) // flatten a union
    {
      INVARIANT(
        boolbv_width(src_type) == boolbv_width(dest_type),
        "bit vector with of source and destination type shall be equal");
      convert_expr(src); // nothing else to do!
    }
    else if(src_type.id()==ID_c_bit_field)
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        convert_expr(src); // ignore
      else
      {
        typet t=c_bit_field_replacement_type(to_c_bit_field_type(src_type), ns);
        typecast_exprt tmp(typecast_exprt(src, t), dest_type);
        convert_typecast(tmp);
      }
    }
    else
    {
      std::ostringstream e_str;
      e_str << src_type.id() << " -> " << dest_type.id()
            << " src == " << format(src);
      UNEXPECTEDCASE("TODO typecast2 " + e_str.str());
    }
  }
  else if(dest_type.id()==ID_fixedbv) // to fixedbv
  {
    const fixedbv_typet &fixedbv_type=to_fixedbv_type(dest_type);
    std::size_t to_fraction_bits=fixedbv_type.get_fraction_bits();
    std::size_t to_integer_bits=fixedbv_type.get_integer_bits();

    if(src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_signedbv ||
       src_type.id()==ID_c_enum)
    {
      // integer to fixedbv

      std::size_t from_width=to_bitvector_type(src_type).get_width();
      out << "(concat ";

      if(from_width==to_integer_bits)
        convert_expr(src);
      else if(from_width>to_integer_bits)
      {
        // too many integer bits
        out << "((_ extract " << (to_integer_bits-1) << " 0) ";
        convert_expr(src);
        out << ")";
      }
      else
      {
        // too few integer bits
        INVARIANT(
          from_width < to_integer_bits,
          "from_width should be smaller than to_integer_bits as other case "
          "have been handled above");
        if(dest_type.id()==ID_unsignedbv)
        {
          out << "(_ zero_extend "
              << (to_integer_bits-from_width) << ") ";
          convert_expr(src);
          out << ")";
        }
        else
        {
          out << "((_ sign_extend "
              << (to_integer_bits-from_width) << ") ";
          convert_expr(src);
          out << ")";
        }
      }

      out << "(_ bv0 " << to_fraction_bits << ")";
      out << ")"; // concat
    }
    else if(src_type.id()==ID_bool) // bool to fixedbv
    {
      out << "(concat (concat"
          << " (_ bv0 " << (to_integer_bits-1) << ") ";
      flatten2bv(src); // produces #b0 or #b1
      out << ") (_ bv0 "
          << to_fraction_bits
          << "))";
    }
    else if(src_type.id()==ID_fixedbv) // fixedbv to fixedbv
    {
      const fixedbv_typet &from_fixedbv_type=to_fixedbv_type(src_type);
      std::size_t from_fraction_bits=from_fixedbv_type.get_fraction_bits();
      std::size_t from_integer_bits=from_fixedbv_type.get_integer_bits();
      std::size_t from_width=from_fixedbv_type.get_width();

      out << "(let ((?tcop ";
      convert_expr(src);
      out << ")) ";

      out << "(concat ";

      if(to_integer_bits<=from_integer_bits)
      {
        out << "((_ extract "
            << (from_fraction_bits+to_integer_bits-1) << " "
            << from_fraction_bits
            << ") ?tcop)";
      }
      else
      {
        INVARIANT(
          to_integer_bits > from_integer_bits,
          "to_integer_bits should be greater than from_integer_bits as the"
          "other case has been handled above");
        out << "((_ sign_extend "
            << (to_integer_bits-from_integer_bits)
            << ") ((_ extract "
            << (from_width-1) << " "
            << from_fraction_bits
            << ") ?tcop))";
      }

      out << " ";

      if(to_fraction_bits<=from_fraction_bits)
      {
        out << "((_ extract "
            << (from_fraction_bits-1) << " "
            << (from_fraction_bits-to_fraction_bits)
            << ") ?tcop)";
      }
      else
      {
        INVARIANT(
          to_fraction_bits > from_fraction_bits,
          "to_fraction_bits should be greater than from_fraction_bits as the"
          "other case has been handled above");
        out << "(concat ((_ extract "
            << (from_fraction_bits-1) << " 0) ";
        convert_expr(src);
        out << ")"
            << " (_ bv0 " << to_fraction_bits-from_fraction_bits
            << "))";
      }

      out << "))"; // concat, let
    }
    else
      UNEXPECTEDCASE("unexpected typecast to fixedbv");
  }
  else if(dest_type.id()==ID_pointer)
  {
    std::size_t to_width=boolbv_width(dest_type);

    if(src_type.id()==ID_pointer) // pointer to pointer
    {
      // this just passes through
      convert_expr(src);
    }
    else if(
      src_type.id() == ID_unsignedbv || src_type.id() == ID_signedbv ||
      src_type.id() == ID_bv)
    {
      // integer to pointer

      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        convert_expr(src);
      else if(from_width<to_width)
      {
        out << "((_ sign_extend "
            << (to_width-from_width)
            << ") ";
        convert_expr(src);
        out << ")"; // sign_extend
      }
      else // from_width>to_width
      {
        out << "((_ extract " << to_width << " 0) ";
        convert_expr(src);
        out << ")"; // extract
      }
    }
    else
      UNEXPECTEDCASE("TODO typecast3 "+src_type.id_string()+" -> pointer");
  }
  else if(dest_type.id()==ID_range)
  {
    SMT2_TODO("range typecast");
  }
  else if(dest_type.id()==ID_floatbv)
  {
    // Typecast from integer to floating-point should have be been
    // converted to ID_floatbv_typecast during symbolic execution,
    // adding the rounding mode.  See
    // smt2_convt::convert_floatbv_typecast.
    // The exception is bool and c_bool to float.
    const auto &dest_floatbv_type = to_floatbv_type(dest_type);

    if(src_type.id()==ID_bool)
    {
      constant_exprt val(irep_idt(), dest_type);

      ieee_floatt a(dest_floatbv_type);

      mp_integer significand;
      mp_integer exponent;

      out << "(ite ";
      convert_expr(src);
      out << " ";

      significand = 1;
      exponent = 0;
      a.build(significand, exponent);
      val.set_value(integer2bvrep(a.pack(), a.spec.width()));

      convert_constant(val);
      out << " ";

      significand = 0;
      exponent = 0;
      a.build(significand, exponent);
      val.set_value(integer2bvrep(a.pack(), a.spec.width()));

      convert_constant(val);
      out << ")";
    }
    else if(src_type.id()==ID_c_bool)
    {
      // turn into proper bool
      const typecast_exprt tmp(src, bool_typet());
      convert_typecast(typecast_exprt(tmp, dest_type));
    }
    else if(src_type.id() == ID_bv)
    {
      if(to_bv_type(src_type).get_width() != dest_floatbv_type.get_width())
      {
        UNEXPECTEDCASE("Typecast bv -> float with wrong width");
      }

      if(use_FPA_theory)
      {
        out << "((_ to_fp " << dest_floatbv_type.get_e() << " "
            << dest_floatbv_type.get_f() + 1 << ") ";
        convert_expr(src);
        out << ')';
      }
      else
        convert_expr(src);
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> float");
  }
  else if(dest_type.id()==ID_integer)
  {
    if(src_type.id()==ID_bool)
    {
      out << "(ite ";
      convert_expr(src);
      out <<" 1 0)";
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> integer");
  }
  else if(dest_type.id()==ID_c_bit_field)
  {
    std::size_t from_width=boolbv_width(src_type);
    std::size_t to_width=boolbv_width(dest_type);

    if(from_width==to_width)
      convert_expr(src); // ignore
    else
    {
      typet t=c_bit_field_replacement_type(to_c_bit_field_type(dest_type), ns);
      typecast_exprt tmp(typecast_exprt(src, t), dest_type);
      convert_typecast(tmp);
    }
  }
  else
    UNEXPECTEDCASE(
      "TODO typecast8 "+src_type.id_string()+" -> "+dest_type.id_string());
}

void smt2_convt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  const exprt &src=expr.op();
  // const exprt &rounding_mode=expr.rounding_mode();
  const typet &src_type=src.type();
  const typet &dest_type=expr.type();

  if(dest_type.id()==ID_floatbv)
  {
    if(src_type.id()==ID_floatbv)
    {
      // float to float

      /* ISO 9899:1999
       * 6.3.1.5 Real floating types
       * 1 When a float is promoted to double or long double, or a
       * double is promoted to long double, its value is unchanged.
       *
       * 2 When a double is demoted to float, a long double is
       * demoted to double or float, or a value being represented in
       * greater precision and range than required by its semantic
       * type (see 6.3.1.8) is explicitly converted to its semantic
       * type, if the value being converted can be represented
       * exactly in the new type, it is unchanged. If the value
       * being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result
       * is either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that
       * can be represented, the behavior is undefined.
       */

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      if(use_FPA_theory)
      {
        out << "((_ to_fp " << dst.get_e() << " "
            << dst.get_f() + 1 << ") ";
        convert_rounding_mode_FPA(expr.op1());
        out << " ";
        convert_expr(src);
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else if(src_type.id()==ID_unsignedbv)
    {
      // unsigned to float

      /* ISO 9899:1999
       * 6.3.1.4 Real floating and integer
       * 2 When a value of integer type is converted to a real
       * floating type, if the value being converted can be
       * represented exactly in the new type, it is unchanged. If the
       * value being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result is
       * either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that can
       * be represented, the behavior is undefined.
       */

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      if(use_FPA_theory)
      {
        out << "((_ to_fp_unsigned " << dst.get_e() << " "
            << dst.get_f() + 1 << ") ";
        convert_rounding_mode_FPA(expr.op1());
        out << " ";
        convert_expr(src);
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else if(src_type.id()==ID_signedbv)
    {
      // signed to float

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      if(use_FPA_theory)
      {
        out << "((_ to_fp " << dst.get_e() << " "
            << dst.get_f() + 1 << ") ";
        convert_rounding_mode_FPA(expr.op1());
        out << " ";
        convert_expr(src);
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else if(src_type.id()==ID_c_enum_tag)
    {
      // enum to float

      // We first convert to 'underlying type'
      floatbv_typecast_exprt tmp=expr;
      tmp.op() = typecast_exprt(
        src, ns.follow_tag(to_c_enum_tag_type(src_type)).underlying_type());
      convert_floatbv_typecast(tmp);
    }
    else
      UNEXPECTEDCASE(
        "TODO typecast11 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  else if(dest_type.id()==ID_signedbv)
  {
    if(use_FPA_theory)
    {
      std::size_t dest_width=to_signedbv_type(dest_type).get_width();
      out << "((_ fp.to_sbv " << dest_width << ") ";
      convert_rounding_mode_FPA(expr.op1());
      out << " ";
      convert_expr(src);
      out << ")";
    }
    else
      convert_floatbv(expr);
  }
  else if(dest_type.id()==ID_unsignedbv)
  {
    if(use_FPA_theory)
    {
      std::size_t dest_width=to_unsignedbv_type(dest_type).get_width();
      out << "((_ fp.to_ubv " << dest_width << ") ";
      convert_rounding_mode_FPA(expr.op1());
      out << " ";
      convert_expr(src);
      out << ")";
    }
    else
      convert_floatbv(expr);
  }
  else
  {
    UNEXPECTEDCASE(
      "TODO typecast12 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
}

void smt2_convt::convert_struct(const struct_exprt &expr)
{
  const struct_typet &struct_type = to_struct_type(ns.follow(expr.type()));

  const struct_typet::componentst &components=
    struct_type.components();

  DATA_INVARIANT(
    components.size() == expr.operands().size(),
    "number of struct components as indicated by the struct type shall be equal"
    "to the number of operands of the struct expression");

  DATA_INVARIANT(!components.empty(), "struct shall have struct components");

  if(use_datatypes)
  {
    const std::string &smt_typename = datatype_map.at(struct_type);

    // use the constructor for the Z3 datatype
    out << "(mk-" << smt_typename;

    std::size_t i=0;
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++, i++)
    {
      if(is_zero_width(it->type(), ns))
        continue;
      out << " ";
      convert_expr(expr.operands()[i]);
    }

    out << ")";
  }
  else
  {
    auto convert_operand = [this](const exprt &op) {
      // may need to flatten array-theory arrays in there
      if(op.type().id() == ID_array && use_array_theory(op))
        flatten_array(op);
      else if(op.type().id() == ID_bool)
        flatten2bv(op);
      else
        convert_expr(op);
    };

    // SMT-LIB 2 concat is binary only
    std::size_t n_concat = 0;
    for(std::size_t i = components.size(); i > 1; i--)
    {
      if(is_zero_width(components[i - 1].type(), ns))
        continue;
      else if(i > 2 || !is_zero_width(components[0].type(), ns))
      {
        ++n_concat;
        out << "(concat ";
      }

      convert_operand(expr.operands()[i - 1]);

      out << " ";
    }

    if(!is_zero_width(components[0].type(), ns))
      convert_operand(expr.op0());

    out << std::string(n_concat, ')');
  }
}

/// produce a flat bit-vector for a given array of fixed size
void smt2_convt::flatten_array(const exprt &expr)
{
  const array_typet &array_type = to_array_type(expr.type());
  const auto &size_expr = array_type.size();
  PRECONDITION(size_expr.is_constant());

  mp_integer size = numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
  CHECK_RETURN_WITH_DIAGNOSTICS(size != 0, "can't convert zero-sized array");

  out << "(let ((?far ";
  convert_expr(expr);
  out << ")) ";

  for(mp_integer i=size; i!=0; --i)
  {
    if(i!=1)
      out << "(concat ";
    out << "(select ?far ";
    convert_expr(from_integer(i - 1, array_type.index_type()));
    out << ")";
    if(i!=1)
      out << " ";
  }

  // close the many parentheses
  for(mp_integer i=size; i>1; --i)
    out << ")";

  out << ")"; // let
}

void smt2_convt::convert_union(const union_exprt &expr)
{
  const union_typet &union_type = to_union_type(ns.follow(expr.type()));
  const exprt &op=expr.op();

  std::size_t total_width=boolbv_width(union_type);

  std::size_t member_width=boolbv_width(op.type());

  if(total_width==member_width)
  {
    flatten2bv(op);
  }
  else
  {
    // we will pad with zeros, but non-det would be better
    INVARIANT(
      total_width > member_width,
      "total_width should be greater than member_width as member_width can be"
      "at most as large as total_width and the other case has been handled "
      "above");
    out << "(concat ";
    out << "(_ bv0 "
        << (total_width-member_width) << ") ";
    flatten2bv(op);
    out << ")";
  }
}

void smt2_convt::convert_constant(const constant_exprt &expr)
{
  const typet &expr_type=expr.type();

  if(expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_bv ||
     expr_type.id()==ID_c_enum ||
     expr_type.id()==ID_c_enum_tag ||
     expr_type.id()==ID_c_bool ||
     expr_type.id()==ID_c_bit_field)
  {
    const std::size_t width = boolbv_width(expr_type);

    const mp_integer value = bvrep2integer(expr.get_value(), width, false);

    out << "(_ bv" << value
        << " " << width << ")";
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    const fixedbv_spect spec(to_fixedbv_type(expr_type));

    const mp_integer v = bvrep2integer(expr.get_value(), spec.width, false);

    out << "(_ bv" << v << " " << spec.width << ")";
  }
  else if(expr_type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=
      to_floatbv_type(expr_type);

    if(use_FPA_theory)
    {
      /* CBMC stores floating point literals in the most
         computationally useful form; biased exponents and
         significands including the hidden bit.  Thus some encoding
         is needed to get to IEEE-754 style representations. */

      ieee_floatt v=ieee_floatt(expr);
      size_t e=floatbv_type.get_e();
      size_t f=floatbv_type.get_f()+1;

      /* Should be sufficient, but not currently supported by mathsat */
      #if 0
      mp_integer binary = v.pack();

      out << "((_ to_fp " << e << " " << f << ")"
          << " #b" << integer2binary(v.pack(), v.spec.width()) << ")";
      #endif

      if(v.is_NaN())
      {
        out << "(_ NaN " << e << " " << f << ")";
      }
      else if(v.is_infinity())
      {
        if(v.get_sign())
          out << "(_ -oo " << e << " " << f << ")";
        else
          out << "(_ +oo " << e << " " << f << ")";
      }
      else
      {
        // Zero, normal or subnormal

        mp_integer binary = v.pack();
        std::string binaryString(integer2binary(v.pack(), v.spec.width()));

        out << "(fp "
            << "#b" << binaryString.substr(0, 1) << " "
            << "#b" << binaryString.substr(1, e) << " "
            << "#b" << binaryString.substr(1+e, f-1) << ")";
      }
    }
    else
    {
      // produce corresponding bit-vector
      const ieee_float_spect spec(floatbv_type);
      const mp_integer v = bvrep2integer(expr.get_value(), spec.width(), false);
      out << "(_ bv" << v << " " << spec.width() << ")";
    }
  }
  else if(expr_type.id()==ID_pointer)
  {
    if(is_null_pointer(expr))
    {
      out << "(_ bv0 " << boolbv_width(expr_type)
          << ")";
    }
    else
    {
      // just treat the pointer as a bit vector
      const std::size_t width = boolbv_width(expr_type);

      const mp_integer value = bvrep2integer(expr.get_value(), width, false);

      out << "(_ bv" << value << " " << width << ")";
    }
  }
  else if(expr_type.id()==ID_bool)
  {
    if(expr.is_true())
      out << "true";
    else if(expr.is_false())
      out << "false";
    else
      UNEXPECTEDCASE("unknown Boolean constant");
  }
  else if(expr_type.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    out << it->second;
  }
  else if(expr_type.id()==ID_rational)
  {
    std::string value=id2string(expr.get_value());
    const bool negative = has_prefix(value, "-");

    if(negative)
      out << "(- ";

    size_t pos=value.find("/");

    if(pos==std::string::npos)
      out << value << ".0";
    else
    {
      out << "(/ " << value.substr(0, pos) << ".0 "
                   << value.substr(pos+1) << ".0)";
    }

    if(negative)
      out << ')';
  }
  else if(expr_type.id()==ID_integer)
  {
    const auto value = id2string(expr.get_value());

    // SMT2 has no negative integer literals
    if(has_prefix(value, "-"))
      out << "(- " << value.substr(1, std::string::npos) << ')';
    else
      out << value;
  }
  else
    UNEXPECTEDCASE("unknown constant: "+expr_type.id_string());
}

void smt2_convt::convert_euclidean_mod(const euclidean_mod_exprt &expr)
{
  if(expr.type().id() == ID_integer)
  {
    out << "(mod ";
    convert_expr(expr.op0());
    out << ' ';
    convert_expr(expr.op1());
    out << ')';
  }
  else
    UNEXPECTEDCASE(
      "unsupported type for euclidean_mod: " + expr.type().id_string());
}

void smt2_convt::convert_mod(const mod_exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      out << "(bvurem ";
    else
      out << "(bvsrem ";

    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else
    UNEXPECTEDCASE("unsupported type for mod: "+expr.type().id_string());
}

void smt2_convt::convert_is_dynamic_object(const unary_exprt &expr)
{
  std::vector<mp_integer> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  if(dynamic_objects.empty())
    out << "false";
  else
  {
    std::size_t pointer_width = boolbv_width(expr.op().type());

    out << "(let ((?obj ((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(expr.op());
    out << "))) ";

    if(dynamic_objects.size()==1)
    {
      out << "(= (_ bv" << dynamic_objects.front()
          << " " << config.bv_encoding.object_bits << ") ?obj)";
    }
    else
    {
      out << "(or";

      for(const auto &object : dynamic_objects)
        out << " (= (_ bv" << object
            << " " << config.bv_encoding.object_bits << ") ?obj)";

      out << ")"; // or
    }

    out << ")"; // let
  }
}

void smt2_convt::convert_relation(const binary_relation_exprt &expr)
{
  const typet &op_type=expr.op0().type();

  if(op_type.id()==ID_unsignedbv ||
     op_type.id()==ID_bv)
  {
    out << "(";
    if(expr.id()==ID_le)
      out << "bvule";
    else if(expr.id()==ID_lt)
      out << "bvult";
    else if(expr.id()==ID_ge)
      out << "bvuge";
    else if(expr.id()==ID_gt)
      out << "bvugt";

    out << " ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(op_type.id()==ID_signedbv ||
          op_type.id()==ID_fixedbv)
  {
    out << "(";
    if(expr.id()==ID_le)
      out << "bvsle";
    else if(expr.id()==ID_lt)
      out << "bvslt";
    else if(expr.id()==ID_ge)
      out << "bvsge";
    else if(expr.id()==ID_gt)
      out << "bvsgt";

    out << " ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(op_type.id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      out << "(";
      if(expr.id()==ID_le)
        out << "fp.leq";
      else if(expr.id()==ID_lt)
        out << "fp.lt";
      else if(expr.id()==ID_ge)
        out << "fp.geq";
      else if(expr.id()==ID_gt)
        out << "fp.gt";

      out << " ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
      convert_floatbv(expr);
  }
  else if(op_type.id()==ID_rational ||
          op_type.id()==ID_integer)
  {
    out << "(";
    out << expr.id();

    out << " ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(op_type.id() == ID_pointer)
  {
    const exprt same_object = ::same_object(expr.op0(), expr.op1());

    out << "(and ";
    convert_expr(same_object);

    out << " (";
    if(expr.id() == ID_le)
      out << "bvsle";
    else if(expr.id() == ID_lt)
      out << "bvslt";
    else if(expr.id() == ID_ge)
      out << "bvsge";
    else if(expr.id() == ID_gt)
      out << "bvsgt";

    out << ' ';
    convert_expr(pointer_offset(expr.op0()));
    out << ' ';
    convert_expr(pointer_offset(expr.op1()));
    out << ')';

    out << ')';
  }
  else
    UNEXPECTEDCASE(
      "unsupported type for "+expr.id_string()+": "+op_type.id_string());
}

void smt2_convt::convert_plus(const plus_exprt &expr)
{
  if(
    expr.type().id() == ID_rational || expr.type().id() == ID_integer ||
    expr.type().id() == ID_real)
  {
    // these are multi-ary in SMT-LIB2
    out << "(+";

    for(const auto &op : expr.operands())
    {
      out << ' ';
      convert_expr(op);
    }

    out << ')';
  }
  else if(
    expr.type().id() == ID_unsignedbv || expr.type().id() == ID_signedbv ||
    expr.type().id() == ID_fixedbv)
  {
    // These could be chained, i.e., need not be binary,
    // but at least MathSat doesn't like that.
    if(expr.operands().size() == 2)
    {
      out << "(bvadd ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
    {
      convert_plus(to_plus_expr(make_binary(expr)));
    }
  }
  else if(expr.type().id() == ID_floatbv)
  {
    // Floating-point additions should have be been converted
    // to ID_floatbv_plus during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_plus.
    UNREACHABLE;
  }
  else if(expr.type().id() == ID_pointer)
  {
    if(expr.operands().size() == 2)
    {
      exprt p = expr.op0(), i = expr.op1();

      if(p.type().id() != ID_pointer)
        p.swap(i);

      DATA_INVARIANT(
        p.type().id() == ID_pointer,
        "one of the operands should have pointer type");

      const auto &base_type = to_pointer_type(expr.type()).base_type();
      DATA_INVARIANT(
        base_type.id() != ID_empty, "no pointer arithmetic over void pointers");

      auto element_size_opt = pointer_offset_size(base_type, ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt >= 0);
      mp_integer element_size = *element_size_opt;

      // First convert the pointer operand
      out << "(let ((?pointerop ";
      convert_expr(p);
      out << ")) ";

      // The addition is done on the offset part only.
      const std::size_t pointer_width = boolbv_width(p.type());
      const std::size_t offset_bits =
        pointer_width - config.bv_encoding.object_bits;

      out << "(concat ";
      out << "((_ extract " << pointer_width - 1 << ' ' << offset_bits
          << ") ?pointerop) ";
      out << "(bvadd ((_ extract " << offset_bits - 1 << " 0) ?pointerop) ";

      if(element_size >= 2)
      {
        out << "(bvmul ((_ extract " << offset_bits - 1 << " 0) ";
        convert_expr(i);
        out << ") (_ bv" << element_size << " " << offset_bits << "))";
      }
      else
      {
        out << "((_ extract " << offset_bits - 1 << " 0) ";
        convert_expr(i);
        out << ')'; // extract
      }

      out << ")))"; // bvadd, concat, let
    }
    else
    {
      convert_plus(to_plus_expr(make_binary(expr)));
    }
  }
  else
    UNEXPECTEDCASE("unsupported type for +: " + expr.type().id_string());
}

/// Converting a constant or symbolic rounding mode to SMT-LIB. Only called when
/// use_FPA_theory is enabled. SMT-LIB output to is sent to `out`.
/// \par parameters: The expression representing the rounding mode.
void smt2_convt::convert_rounding_mode_FPA(const exprt &expr)
{
  PRECONDITION(use_FPA_theory);

  /* CProver uses the x86 numbering of the rounding-mode
   *   0 == FE_TONEAREST
   *   1 == FE_DOWNWARD
   *   2 == FE_UPWARD
   *   3 == FE_TOWARDZERO
   * These literal values must be used rather than the macros
   * the macros from fenv.h to avoid portability problems.
   */

  if(expr.is_constant())
  {
    const constant_exprt &cexpr=to_constant_expr(expr);

    mp_integer value = numeric_cast_v<mp_integer>(cexpr);

    if(value==0)
      out << "roundNearestTiesToEven";
    else if(value==1)
      out << "roundTowardNegative";
    else if(value==2)
      out << "roundTowardPositive";
    else if(value==3)
      out << "roundTowardZero";
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "Rounding mode should have value 0, 1, 2, or 3",
        id2string(cexpr.get_value()));
  }
  else
  {
    std::size_t width=to_bitvector_type(expr.type()).get_width();

    // Need to make the choice above part of the model
    out << "(ite (= (_ bv0 " << width << ") ";
    convert_expr(expr);
    out << ") roundNearestTiesToEven ";

    out << "(ite (= (_ bv1 " << width << ") ";
    convert_expr(expr);
    out << ") roundTowardNegative ";

    out << "(ite (= (_ bv2 " << width << ") ";
    convert_expr(expr);
    out << ") roundTowardPositive ";

    // TODO: add some kind of error checking here
    out << "roundTowardZero";

    out << ")))";
  }
}

void smt2_convt::convert_floatbv_plus(const ieee_float_op_exprt &expr)
{
  const typet &type=expr.type();

  PRECONDITION(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex &&
     to_complex_type(type).subtype().id() == ID_floatbv));

  if(use_FPA_theory)
  {
    if(type.id()==ID_floatbv)
    {
      out << "(fp.add ";
      convert_rounding_mode_FPA(expr.rounding_mode());
      out << " ";
      convert_expr(expr.lhs());
      out << " ";
      convert_expr(expr.rhs());
      out << ")";
    }
    else if(type.id()==ID_complex)
    {
      SMT2_TODO("+ for floatbv complex");
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "type should not be one of the unsupported types",
        type.id_string());
  }
  else
    convert_floatbv(expr);
}

void smt2_convt::convert_minus(const minus_exprt &expr)
{
  if(expr.type().id()==ID_integer)
  {
    out << "(- ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    if(expr.op0().type().id()==ID_pointer &&
       expr.op1().type().id()==ID_pointer)
    {
      // Pointer difference
      const auto &base_type = to_pointer_type(expr.op0().type()).base_type();
      DATA_INVARIANT(
        base_type.id() != ID_empty, "no pointer arithmetic over void pointers");
      auto element_size_opt = pointer_offset_size(base_type, ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt >= 1);
      mp_integer element_size = *element_size_opt;

      if(element_size >= 2)
        out << "(bvsdiv ";

      INVARIANT(
        boolbv_width(expr.op0().type()) == boolbv_width(expr.type()),
        "bitvector width of operand shall be equal to the bitvector width of "
        "the expression");

      out << "(bvsub ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";

      if(element_size >= 2)
        out << " (_ bv" << element_size << " " << boolbv_width(expr.type())
            << "))";
    }
    else
    {
      out << "(bvsub ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point subtraction should have be been converted
    // to ID_floatbv_minus during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_minus.
    UNREACHABLE;
  }
  else if(expr.type().id()==ID_pointer)
  {
    if(
      expr.op0().type().id() == ID_pointer &&
      (expr.op1().type().id() == ID_unsignedbv ||
       expr.op1().type().id() == ID_signedbv))
    {
      // rewrite p-o to p+(-o)
      return convert_plus(
        plus_exprt(expr.op0(), unary_minus_exprt(expr.op1())));
    }
    else
      UNEXPECTEDCASE(
        "unsupported operand types for -: " + expr.op0().type().id_string() +
        " and " + expr.op1().type().id_string());
  }
  else
    UNEXPECTEDCASE("unsupported type for -: "+expr.type().id_string());
}

void smt2_convt::convert_floatbv_minus(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    out << "(fp.sub ";
    convert_rounding_mode_FPA(expr.rounding_mode());
    out << " ";
    convert_expr(expr.lhs());
    out << " ";
    convert_expr(expr.rhs());
    out << ")";
  }
  else
    convert_floatbv(expr);
}

void smt2_convt::convert_div(const div_exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      out << "(bvudiv ";
    else
      out << "(bvsdiv ";

    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));
    std::size_t fraction_bits=spec.get_fraction_bits();

    out << "((_ extract " << spec.width-1 << " 0) ";
    out << "(bvsdiv ";

    out << "(concat ";
    convert_expr(expr.op0());
    out << " (_ bv0 " << fraction_bits << ")) ";

    out << "((_ sign_extend " << fraction_bits << ") ";
    convert_expr(expr.op1());
    out << ")";

    out << "))";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point division should have be been converted
    // to ID_floatbv_div during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_div.
    UNREACHABLE;
  }
  else
    UNEXPECTEDCASE("unsupported type for /: "+expr.type().id_string());
}

void smt2_convt::convert_floatbv_div(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    out << "(fp.div ";
    convert_rounding_mode_FPA(expr.rounding_mode());
    out << " ";
    convert_expr(expr.lhs());
    out << " ";
    convert_expr(expr.rhs());
    out << ")";
  }
  else
    convert_floatbv(expr);
}

void smt2_convt::convert_mult(const mult_exprt &expr)
{
  // re-write to binary if needed
  if(expr.operands().size()>2)
  {
    // strip last operand
    exprt tmp=expr;
    tmp.operands().pop_back();

    // recursive call
    return convert_mult(mult_exprt(tmp, expr.operands().back()));
  }

  INVARIANT(
    expr.operands().size() == 2,
    "expression should have been converted to a variant with two operands");

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    // Note that bvmul is really unsigned,
    // but this is irrelevant as we chop-off any extra result
    // bits.
    out << "(bvmul ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point multiplication should have be been converted
    // to ID_floatbv_mult during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_mult.
    UNREACHABLE;
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));
    std::size_t fraction_bits=spec.get_fraction_bits();

    out << "((_ extract "
        << spec.width+fraction_bits-1 << " "
        << fraction_bits << ") ";

    out << "(bvmul ";

    out << "((_ sign_extend " << fraction_bits << ") ";
    convert_expr(expr.op0());
    out << ") ";

    out << "((_ sign_extend " << fraction_bits << ") ";
    convert_expr(expr.op1());
    out << ")";

    out << "))"; // bvmul, extract
  }
  else if(expr.type().id()==ID_rational ||
          expr.type().id()==ID_integer ||
          expr.type().id()==ID_real)
  {
    out << "(*";

    for(const auto &op : expr.operands())
    {
      out << " ";
      convert_expr(op);
    }

    out << ")";
  }
  else
    UNEXPECTEDCASE("unsupported type for *: "+expr.type().id_string());
}

void smt2_convt::convert_floatbv_mult(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    out << "(fp.mul ";
    convert_rounding_mode_FPA(expr.rounding_mode());
    out << " ";
    convert_expr(expr.lhs());
    out << " ";
    convert_expr(expr.rhs());
    out << ")";
  }
  else
    convert_floatbv(expr);
}

void smt2_convt::convert_floatbv_rem(const binary_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    // Note that these do not have a rounding mode
    out << "(fp.rem ";
    convert_expr(expr.lhs());
    out << " ";
    convert_expr(expr.rhs());
    out << ")";
  }
  else
  {
    SMT2_TODO(
      "smt2_convt::convert_floatbv_rem to be implemented when not using "
      "FPA_theory");
  }
}

void smt2_convt::convert_with(const with_exprt &expr)
{
  // get rid of "with" that has more than three operands

  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();

    // strip off the trailing two operands
    with_exprt tmp = expr;
    tmp.operands().resize(s-2);

    with_exprt new_with_expr(
      tmp, expr.operands()[s - 2], expr.operands().back());

    // recursive call
    return convert_with(new_with_expr);
  }

  INVARIANT(
    expr.operands().size() == 3,
    "with expression should have been converted to a version with three "
    "operands above");

  const typet &expr_type = expr.type();

  if(expr_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(expr_type);

    if(use_array_theory(expr))
    {
      out << "(store ";
      convert_expr(expr.old());
      out << " ";
      convert_expr(typecast_exprt(expr.where(), array_type.index_type()));
      out << " ";
      convert_expr(expr.new_value());
      out << ")";
    }
    else
    {
      // fixed-width
      std::size_t array_width=boolbv_width(array_type);
      std::size_t sub_width = boolbv_width(array_type.element_type());
      std::size_t index_width=boolbv_width(expr.where().type());

      // We mask out the updated bits with AND,
      // and then OR-in the shifted new value.

      out << "(let ((distance? ";
      out << "(bvmul (_ bv" << sub_width << " " << array_width << ") ";

      // SMT2 says that the shift distance needs to be as wide
      // as the stuff we are shifting.
      if(array_width>index_width)
      {
        out << "((_ zero_extend " << array_width-index_width << ") ";
        convert_expr(expr.where());
        out << ")";
      }
      else
      {
        out << "((_ extract " << array_width-1 << " 0) ";
        convert_expr(expr.where());
        out << ")";
      }

      out << "))) "; // bvmul, distance?

      out << "(bvor ";
      out << "(bvand ";
      out << "(bvnot ";
      out << "(bvshl (_ bv" << power(2, sub_width) - 1 << " " << array_width
          << ") ";
      out << "distance?)) "; // bvnot, bvlshl
      convert_expr(expr.old());
      out << ") "; // bvand
      out << "(bvshl ";
      out << "((_ zero_extend " << array_width-sub_width << ") ";
      convert_expr(expr.new_value());
      out << ") distance?)))"; // zero_extend, bvshl, bvor, let
    }
  }
  else if(expr_type.id() == ID_struct || expr_type.id() == ID_struct_tag)
  {
    const struct_typet &struct_type = to_struct_type(ns.follow(expr_type));

    const exprt &index = expr.where();
    const exprt &value = expr.new_value();

    const irep_idt &component_name=index.get(ID_component_name);

    INVARIANT(
      struct_type.has_component(component_name),
      "struct should have accessed component");

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(expr_type);

      out << "(update-" << smt_typename << "." << component_name << " ";
      convert_expr(expr.old());
      out << " ";
      convert_expr(value);
      out << ")";
    }
    else
    {
      std::size_t struct_width=boolbv_width(struct_type);

      // figure out the offset and width of the member
      const boolbv_widtht::membert &m =
        boolbv_width.get_member(struct_type, component_name);

      out << "(let ((?withop ";
      convert_expr(expr.old());
      out << ")) ";

      if(m.width==struct_width)
      {
        // the struct is the same as the member, no concat needed,
        // ?withop won't be used
        convert_expr(value);
      }
      else if(m.offset==0)
      {
        // the member is at the beginning
        out << "(concat "
            << "((_ extract " << (struct_width-1) << " "
                              << m.width << ") ?withop) ";
        convert_expr(value);
        out << ")"; // concat
      }
      else if(m.offset+m.width==struct_width)
      {
        // the member is at the end
        out << "(concat ";
        convert_expr(value);
        out << " ((_ extract " << (m.offset - 1) << " 0) ?withop))";
      }
      else
      {
        // most general case, need two concat-s
        out << "(concat (concat "
            << "((_ extract " << (struct_width-1) << " "
                              << (m.offset+m.width) << ") ?withop) ";
        convert_expr(value);
        out << ") ((_ extract " << (m.offset-1) << " 0) ?withop)";
        out << ")"; // concat
      }

      out << ")"; // let ?withop
    }
  }
  else if(expr_type.id() == ID_union || expr_type.id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(expr_type));

    const exprt &value = expr.new_value();

    std::size_t total_width=boolbv_width(union_type);

    std::size_t member_width=boolbv_width(value.type());

    if(total_width==member_width)
    {
      flatten2bv(value);
    }
    else
    {
      INVARIANT(
        total_width > member_width,
        "total width should be greater than member_width as member_width is at "
        "most as large as total_width and the other case has been handled "
        "above");
      out << "(concat ";
      out << "((_ extract "
          << (total_width-1)
          << " " << member_width << ") ";
      convert_expr(expr.old());
      out << ") ";
      flatten2bv(value);
      out << ")";
    }
  }
  else if(expr_type.id()==ID_bv ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv)
  {
    // Update bits in a bit-vector. We use masking and shifts.
    const exprt &index = expr.where();
    const exprt &new_value = expr.new_value();

    std::size_t total_width=boolbv_width(expr_type);
    std::size_t value_width = boolbv_width(new_value.type());

    auto index_converted = typecast_exprt::conditional_cast(index, expr_type);

    out << "(bvor ";
    out << "(bvand ";

    // the mask to get rid of the old bits
    out << "(bvnot (bvshl ";
    out << "#b" << std::string(total_width - value_width, '0')
        << std::string(value_width, '1');

    // shift it to the index
    out << ' ';
    convert_expr(index_converted);
    out << "))"; // bvshl, bvnot

    out << ')'; // bvand

    // or-in the new value
    out << " (bvshl ";
    convert_expr(typecast_exprt::conditional_cast(new_value, expr_type));

    // shift it to the index
    out << ' ';
    convert_expr(index_converted);
    out << ')'; // bvshl

    out << ')'; // bvor
  }
  else
    UNEXPECTEDCASE(
      "with expects struct, union, array, or bit-vector type, but got " +
      expr.type().id_string());
}

void smt2_convt::convert_update(const update_exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  SMT2_TODO("smt2_convt::convert_update to be implemented");
}

void smt2_convt::convert_index(const index_exprt &expr)
{
  const typet &array_op_type = expr.array().type();

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(array_op_type);

    if(use_array_theory(expr.array()))
    {
      if(expr.is_boolean() && !use_array_of_bool)
      {
        out << "(= ";
        out << "(select ";
        convert_expr(expr.array());
        out << " ";
        convert_expr(typecast_exprt(expr.index(), array_type.index_type()));
        out << ")";
        out << " #b1)";
      }
      else
      {
        out << "(select ";
        convert_expr(expr.array());
        out << " ";
        convert_expr(typecast_exprt(expr.index(), array_type.index_type()));
        out << ")";
      }
    }
    else
    {
      // fixed size
      std::size_t array_width=boolbv_width(array_type);

      unflatten(wheret::BEGIN, array_type.element_type());

      std::size_t sub_width = boolbv_width(array_type.element_type());
      std::size_t index_width=boolbv_width(expr.index().type());

      out << "((_ extract " << sub_width-1 << " 0) ";
      out << "(bvlshr ";
      convert_expr(expr.array());
      out << " ";
      out << "(bvmul (_ bv" << sub_width << " " << array_width << ") ";

      // SMT2 says that the shift distance must be the same as
      // the width of what we shift.
      if(array_width>index_width)
      {
        out << "((_ zero_extend " << array_width-index_width << ") ";
        convert_expr(expr.index());
        out << ")"; // zero_extend
      }
      else
      {
        out << "((_ extract " << array_width-1 << " 0) ";
        convert_expr(expr.index());
        out << ")"; // extract
      }

      out << ")))"; // mult, bvlshr, extract

      unflatten(wheret::END, array_type.element_type());
    }
  }
  else
    INVARIANT(
      false, "index with unsupported array type: " + array_op_type.id_string());
}

void smt2_convt::convert_member(const member_exprt &expr)
{
  const member_exprt &member_expr=to_member_expr(expr);
  const exprt &struct_op=member_expr.struct_op();
  const typet &struct_op_type = struct_op.type();
  const irep_idt &name=member_expr.get_component_name();

  if(struct_op_type.id() == ID_struct || struct_op_type.id() == ID_struct_tag)
  {
    const struct_typet &struct_type = to_struct_type(ns.follow(struct_op_type));

    INVARIANT(
      struct_type.has_component(name), "struct should have accessed component");

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(struct_type);

      out << "(" << smt_typename << "."
          << struct_type.get_component(name).get_name()
          << " ";
      convert_expr(struct_op);
      out << ")";
    }
    else
    {
      // we extract
      const auto &member_offset = boolbv_width.get_member(struct_type, name);

      if(expr.type().id() == ID_bool)
        out << "(= ";
      out << "((_ extract " << (member_offset.offset + member_offset.width - 1)
          << " " << member_offset.offset << ") ";
      convert_expr(struct_op);
      out << ")";
      if(expr.type().id() == ID_bool)
        out << " #b1)";
    }
  }
  else if(
    struct_op_type.id() == ID_union || struct_op_type.id() == ID_union_tag)
  {
    std::size_t width=boolbv_width(expr.type());
    CHECK_RETURN_WITH_DIAGNOSTICS(
      width != 0, "failed to get union member width");

    unflatten(wheret::BEGIN, expr.type());

    out << "((_ extract "
           << (width-1)
           << " 0) ";
    convert_expr(struct_op);
    out << ")";

    unflatten(wheret::END, expr.type());
  }
  else
    UNEXPECTEDCASE(
      "convert_member on an unexpected type "+struct_op_type.id_string());
}

void smt2_convt::flatten2bv(const exprt &expr)
{
  const typet &type = expr.type();

  if(type.id()==ID_bool)
  {
    out << "(ite ";
    convert_expr(expr); // this returns a Bool
    out << " #b1 #b0)"; // this is a one-bit bit-vector
  }
  else if(type.id()==ID_array)
  {
    if(use_array_theory(expr))
    {
      // concatenate elements
      const array_typet &array_type = to_array_type(type);

      mp_integer size =
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

      // SMT-LIB 2 concat is binary only
      std::size_t n_concat = 0;
      for(mp_integer i = size; i > 1; --i)
      {
        ++n_concat;
        out << "(concat ";

        flatten2bv(
          index_exprt{expr, from_integer(i - 1, array_type.index_type())});

        out << " ";
      }

      flatten2bv(index_exprt{expr, from_integer(0, array_type.index_type())});

      out << std::string(n_concat, ')'); // concat
    }
    else
      convert_expr(expr);
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(use_datatypes)
    {
      // concatenate elements
      const struct_typet &struct_type = to_struct_type(ns.follow(type));

      const struct_typet::componentst &components=
        struct_type.components();

      // SMT-LIB 2 concat is binary only
      std::size_t n_concat = 0;
      for(std::size_t i=components.size(); i>1; i--)
      {
        if(is_zero_width(components[i - 1].type(), ns))
          continue;
        else if(i > 2 || !is_zero_width(components[0].type(), ns))
        {
          ++n_concat;
          out << "(concat ";
        }

        flatten2bv(member_exprt{expr, components[i - 1]});

        out << " ";
      }

      if(!is_zero_width(components[0].type(), ns))
      {
        flatten2bv(member_exprt{expr, components[0]});
      }

      out << std::string(n_concat, ')'); // concat
    }
    else
      convert_expr(expr);
  }
  else if(type.id()==ID_floatbv)
  {
    INVARIANT(
      !use_FPA_theory,
      "floatbv expressions should be flattened when using FPA theory");

    convert_expr(expr);
  }
  else
    convert_expr(expr);
}

void smt2_convt::unflatten(
  wheret where,
  const typet &type,
  unsigned nesting)
{
  if(type.id()==ID_bool)
  {
    if(where==wheret::BEGIN)
      out << "(= "; // produces a bool
    else
      out << " #b1)";
  }
  else if(type.id() == ID_array)
  {
    if(use_datatypes)
    {
      PRECONDITION(use_as_const);

      if(where == wheret::BEGIN)
        out << "(let ((?ufop" << nesting << " ";
      else
      {
        out << ")) ";

        const array_typet &array_type = to_array_type(type);

        std::size_t subtype_width = boolbv_width(array_type.element_type());

        DATA_INVARIANT(
          array_type.size().is_constant(),
          "cannot unflatten arrays of non-constant size");
        mp_integer size =
          numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));

        for(mp_integer i = 1; i < size; ++i)
          out << "(store ";

        out << "((as const ";
        convert_type(array_type);
        out << ") ";
        // use element at index 0 as default value
        unflatten(wheret::BEGIN, array_type.element_type(), nesting + 1);
        out << "((_ extract " << subtype_width - 1 << " "
            << "0) ?ufop" << nesting << ")";
        unflatten(wheret::END, array_type.element_type(), nesting + 1);
        out << ") ";

        std::size_t offset = subtype_width;
        for(mp_integer i = 1; i < size; ++i, offset += subtype_width)
        {
          convert_expr(from_integer(i, array_type.index_type()));
          out << ' ';
          unflatten(wheret::BEGIN, array_type.element_type(), nesting + 1);
          out << "((_ extract " << offset + subtype_width - 1 << " " << offset
              << ") ?ufop" << nesting << ")";
          unflatten(wheret::END, array_type.element_type(), nesting + 1);
          out << ")"; // store
        }

        out << ")"; // let
      }
    }
    else
    {
      // nop, already a bv
    }
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(use_datatypes)
    {
      // extract members
      if(where==wheret::BEGIN)
        out << "(let ((?ufop" << nesting << " ";
      else
      {
        out << ")) ";

        const std::string &smt_typename = datatype_map.at(type);

        out << "(mk-" << smt_typename;

        const struct_typet &struct_type = to_struct_type(ns.follow(type));

        const struct_typet::componentst &components=
          struct_type.components();

        std::size_t offset=0;

        std::size_t i=0;
        for(struct_typet::componentst::const_iterator
            it=components.begin();
            it!=components.end();
            it++, i++)
        {
          if(is_zero_width(it->type(), ns))
            continue;

          std::size_t member_width=boolbv_width(it->type());

          out << " ";
          unflatten(wheret::BEGIN, it->type(), nesting+1);
          out << "((_ extract " << offset+member_width-1 << " "
              << offset << ") ?ufop" << nesting << ")";
          unflatten(wheret::END, it->type(), nesting+1);
          offset+=member_width;
        }

        out << "))"; // mk-, let
      }
    }
    else
    {
      // nop, already a bv
    }
  }
  else
  {
    // nop
  }
}

void smt2_convt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.is_boolean());

  if(expr.id()==ID_and && value)
  {
    for(const auto &op : expr.operands())
      set_to(op, true);
    return;
  }

  if(expr.id()==ID_or && !value)
  {
    for(const auto &op : expr.operands())
      set_to(op, false);
    return;
  }

  if(expr.id()==ID_not)
  {
    return set_to(to_not_expr(expr).op(), !value);
  }

  out << "\n";

  // special treatment for "set_to(a=b, true)" where
  // a is a new symbol

  if(expr.id() == ID_equal && value)
  {
    const equal_exprt &equal_expr=to_equal_expr(expr);
    if(is_zero_width(equal_expr.lhs().type(), ns))
    {
      // ignore equality checking over expressions with empty (void) type
      return;
    }

    if(equal_expr.lhs().id()==ID_symbol)
    {
      const irep_idt &identifier=
        to_symbol_expr(equal_expr.lhs()).get_identifier();

      if(
        identifier_map.find(identifier) == identifier_map.end() &&
        equal_expr.lhs() != equal_expr.rhs())
      {
        identifiert &id=identifier_map[identifier];
        CHECK_RETURN(id.type.is_nil());

        id.type=equal_expr.lhs().type();
        find_symbols(id.type);
        exprt prepared_rhs = prepare_for_convert_expr(equal_expr.rhs());

        std::string smt2_identifier=convert_identifier(identifier);
        smt2_identifiers.insert(smt2_identifier);

        out << "; set_to true (equal)\n";

        if(equal_expr.lhs().type().id() == ID_mathematical_function)
        {
          // We avoid define-fun, since it has been reported to cause
          // trouble with Z3's parser.
          out << "(declare-fun " << smt2_identifier;

          auto &mathematical_function_type =
            to_mathematical_function_type(equal_expr.lhs().type());

          out << " (";
          bool first = true;

          for(auto &t : mathematical_function_type.domain())
          {
            if(first)
              first = false;
            else
              out << ' ';

            convert_type(t);
          }

          out << ") ";
          convert_type(mathematical_function_type.codomain());
          out << ")\n";

          out << "(assert (= " << smt2_identifier << ' ';
          convert_expr(prepared_rhs);
          out << ')' << ')' << '\n';
        }
        else
        {
          out << "(define-fun " << smt2_identifier;
          out << " () ";
          if(
            equal_expr.lhs().type().id() != ID_array ||
            use_array_theory(prepared_rhs))
          {
            convert_type(equal_expr.lhs().type());
          }
          else
          {
            std::size_t width = boolbv_width(equal_expr.lhs().type());
            out << "(_ BitVec " << width << ")";
          }
          out << ' ';
          convert_expr(prepared_rhs);
          out << ')' << '\n';
        }

        return; // done
      }
    }
  }

  exprt prepared_expr = prepare_for_convert_expr(expr);

#if 0
  out << "; CONV: "
      << format(expr) << "\n";
#endif

  out << "; set_to " << (value?"true":"false") << "\n"
      << "(assert ";
  if(!value)
  {
    out << "(not ";
  }
  const auto found_literal = defined_expressions.find(expr);
  if(!(found_literal == defined_expressions.end()))
  {
    // This is a converted expression, we can just assert the literal name
    // since the expression is already defined
    out << found_literal->second;
    set_values[found_literal->second] = value;
  }
  else
  {
    convert_expr(prepared_expr);
  }
  if(!value)
  {
    out << ")";
  }
  out << ")\n";
  return;
}

/// Lower byte_update and byte_extract operations within \p expr. Return an
/// equivalent expression that doesn't use byte operators.
/// Note this replaces operators post-order (compare \ref lower_byte_operators,
/// which uses a pre-order walk, replacing in child expressions before the
/// parent). Pre-order replacement currently fails regression tests: see
/// https://github.com/diffblue/cbmc/issues/4380
exprt smt2_convt::lower_byte_operators(const exprt &expr)
{
  exprt lowered_expr = expr;

  for(auto it = lowered_expr.depth_begin(), itend = lowered_expr.depth_end();
      it != itend;
      ++it)
  {
    if(
      it->id() == ID_byte_extract_little_endian ||
      it->id() == ID_byte_extract_big_endian)
    {
      it.mutate() = lower_byte_extract(to_byte_extract_expr(*it), ns);
    }
    else if(
      it->id() == ID_byte_update_little_endian ||
      it->id() == ID_byte_update_big_endian)
    {
      it.mutate() = lower_byte_update(to_byte_update_expr(*it), ns);
    }
  }

  return lowered_expr;
}

/// Perform steps necessary before an expression is passed to \ref convert_expr
/// 1. Replace byte operators (byte_extract, _update) with equivalent
///    expressions
/// 2. Call find_symbols to create auxiliary symbols, e.g. for array
///    expressions.
/// \param expr: expression to prepare
/// \return equivalent expression suitable for convert_expr.
exprt smt2_convt::prepare_for_convert_expr(const exprt &expr)
{
  // First, replace byte operators, because they may introduce new array
  // expressions that must be seen by find_symbols:
  exprt lowered_expr = lower_byte_operators(expr);
  INVARIANT(
    !has_byte_operator(lowered_expr),
    "lower_byte_operators should remove all byte operators");

  // Perform rewrites that may introduce new symbols
  for(auto it = lowered_expr.depth_begin(), itend = lowered_expr.depth_end();
      it != itend;) // no ++it
  {
    if(
      auto prophecy_r_or_w_ok =
        expr_try_dynamic_cast<prophecy_r_or_w_ok_exprt>(*it))
    {
      exprt lowered = simplify_expr(prophecy_r_or_w_ok->lower(ns), ns);
      it.mutate() = lowered;
      it.next_sibling_or_parent();
    }
    else if(
      auto prophecy_pointer_in_range =
        expr_try_dynamic_cast<prophecy_pointer_in_range_exprt>(*it))
    {
      exprt lowered = simplify_expr(prophecy_pointer_in_range->lower(ns), ns);
      it.mutate() = lowered;
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  // Now create symbols for all composite expressions present in lowered_expr:
  find_symbols(lowered_expr);

  return lowered_expr;
}

void smt2_convt::find_symbols(const exprt &expr)
{
  if(is_zero_width(expr.type(), ns))
    return;

  // recursive call on type
  find_symbols(expr.type());

  if(expr.id() == ID_exists || expr.id() == ID_forall)
  {
    // do not declare the quantified symbol, but record
    // as 'bound symbol'
    const auto &q_expr = to_quantifier_expr(expr);
    for(const auto &symbol : q_expr.variables())
    {
      const auto identifier = symbol.get_identifier();
      identifiert &id = identifier_map[identifier];
      id.type = symbol.type();
      id.is_bound = true;
    }
    find_symbols(q_expr.where());
    return;
  }

  // recursive call on operands
  for(const auto &op : expr.operands())
    find_symbols(op);

  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    // we don't track function-typed symbols
    if(expr.type().id()==ID_code)
      return;

    irep_idt identifier;

    if(expr.id()==ID_symbol)
      identifier=to_symbol_expr(expr).get_identifier();
    else
      identifier="nondet_"+
        id2string(to_nondet_symbol_expr(expr).get_identifier());

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      std::string smt2_identifier=convert_identifier(identifier);
      smt2_identifiers.insert(smt2_identifier);

      out << "; find_symbols\n";
      out << "(declare-fun " << smt2_identifier;

      if(expr.type().id() == ID_mathematical_function)
      {
        auto &mathematical_function_type =
          to_mathematical_function_type(expr.type());
        out << " (";
        bool first = true;

        for(auto &type : mathematical_function_type.domain())
        {
          if(first)
            first = false;
          else
            out << ' ';
          convert_type(type);
        }

        out << ") ";
        convert_type(mathematical_function_type.codomain());
      }
      else
      {
        out << " () ";
        convert_type(expr.type());
      }

      out << ")" << "\n";
    }
  }
  else if(expr.id() == ID_array_of)
  {
    if(!use_as_const)
    {
      if(defined_expressions.find(expr) == defined_expressions.end())
      {
        const auto &array_of = to_array_of_expr(expr);
        const auto &array_type = array_of.type();

        const irep_idt id =
          "array_of." + std::to_string(defined_expressions.size());
        out << "; the following is a substitute for lambda i. x\n";
        out << "(declare-fun " << id << " () ";
        convert_type(array_type);
        out << ")\n";

        if(!is_zero_width(array_type.element_type(), ns))
        {
          // use a quantifier-based initialization instead of lambda
          out << "(assert (forall ((i ";
          convert_type(array_type.index_type());
          out << ")) (= (select " << id << " i) ";
          if(array_type.element_type().id() == ID_bool && !use_array_of_bool)
          {
            out << "(ite ";
            convert_expr(array_of.what());
            out << " #b1 #b0)";
          }
          else
          {
            convert_expr(array_of.what());
          }
          out << ")))\n";
        }

        defined_expressions[expr] = id;
      }
    }
  }
  else if(expr.id() == ID_array_comprehension)
  {
    if(!use_lambda_for_array)
    {
      if(defined_expressions.find(expr) == defined_expressions.end())
      {
        const auto &array_comprehension = to_array_comprehension_expr(expr);
        const auto &array_type = array_comprehension.type();
        const auto &array_size = array_type.size();

        const irep_idt id =
          "array_comprehension." + std::to_string(defined_expressions.size());
        out << "(declare-fun " << id << " () ";
        convert_type(array_type);
        out << ")\n";

        out << "; the following is a substitute for lambda i . x(i)\n";
        out << "; universally quantified initialization of the array\n";
        out << "(assert (forall ((";
        convert_expr(array_comprehension.arg());
        out << " ";
        convert_type(array_size.type());
        out << ")) (=> (and (bvule (_ bv0 " << boolbv_width(array_size.type())
            << ") ";
        convert_expr(array_comprehension.arg());
        out << ") (bvult ";
        convert_expr(array_comprehension.arg());
        out << " ";
        convert_expr(array_size);
        out << ")) (= (select " << id << " ";
        convert_expr(array_comprehension.arg());
        out << ") ";
        if(array_type.element_type().id() == ID_bool && !use_array_of_bool)
        {
          out << "(ite ";
          convert_expr(array_comprehension.body());
          out << " #b1 #b0)";
        }
        else
        {
          convert_expr(array_comprehension.body());
        }
        out << "))))\n";

        defined_expressions[expr] = id;
      }
    }
  }
  else if(expr.id()==ID_array)
  {
    if(defined_expressions.find(expr)==defined_expressions.end())
    {
      const array_typet &array_type=to_array_type(expr.type());

      const irep_idt id = "array." + std::to_string(defined_expressions.size());
      out << "; the following is a substitute for an array constructor" << "\n";
      out << "(declare-fun " << id << " () ";
      convert_type(array_type);
      out << ")" << "\n";

      if(!is_zero_width(array_type.element_type(), ns))
      {
        for(std::size_t i = 0; i < expr.operands().size(); i++)
        {
          out << "(assert (= (select " << id << " ";
          convert_expr(from_integer(i, array_type.index_type()));
          out << ") "; // select
          if(array_type.element_type().id() == ID_bool && !use_array_of_bool)
          {
            out << "(ite ";
            convert_expr(expr.operands()[i]);
            out << " #b1 #b0)";
          }
          else
          {
            convert_expr(expr.operands()[i]);
          }
          out << "))"
              << "\n"; // =, assert
        }
      }

      defined_expressions[expr]=id;
    }
  }
  else if(expr.id()==ID_string_constant)
  {
    if(defined_expressions.find(expr)==defined_expressions.end())
    {
      // introduce a temporary array.
      exprt tmp=to_string_constant(expr).to_array_expr();
      const array_typet &array_type=to_array_type(tmp.type());

      const irep_idt id =
        "string." + std::to_string(defined_expressions.size());
      out << "; the following is a substitute for a string" << "\n";
      out << "(declare-fun " << id << " () ";
      convert_type(array_type);
      out << ")" << "\n";

      for(std::size_t i=0; i<tmp.operands().size(); i++)
      {
        out << "(assert (= (select " << id << ' ';
        convert_expr(from_integer(i, array_type.index_type()));
        out << ") "; // select
        convert_expr(tmp.operands()[i]);
        out << "))" << "\n";
      }

      defined_expressions[expr]=id;
    }
  }
  else if(
    const auto object_size = expr_try_dynamic_cast<object_size_exprt>(expr))
  {
    if(object_sizes.find(*object_size) == object_sizes.end())
    {
      const irep_idt id = convert_identifier(
        "object_size." + std::to_string(object_sizes.size()));
      out << "(declare-fun " << id << " () ";
      convert_type(object_size->type());
      out << ")"
          << "\n";

      object_sizes[*object_size] = id;
    }
  }
  // clang-format off
  else if(!use_FPA_theory &&
          expr.operands().size() >= 1 &&
          (expr.id() == ID_floatbv_plus ||
           expr.id() == ID_floatbv_minus ||
           expr.id() == ID_floatbv_mult ||
           expr.id() == ID_floatbv_div ||
           expr.id() == ID_floatbv_typecast ||
           expr.id() == ID_ieee_float_equal ||
           expr.id() == ID_ieee_float_notequal ||
           ((expr.id() == ID_lt ||
             expr.id() == ID_gt ||
             expr.id() == ID_le ||
             expr.id() == ID_ge ||
             expr.id() == ID_isnan ||
             expr.id() == ID_isnormal ||
             expr.id() == ID_isfinite ||
             expr.id() == ID_isinf ||
             expr.id() == ID_sign ||
             expr.id() == ID_unary_minus ||
             expr.id() == ID_typecast ||
             expr.id() == ID_abs) &&
             to_multi_ary_expr(expr).op0().type().id() == ID_floatbv)))
  // clang-format on
  {
    irep_idt function =
      convert_identifier("float_bv." + expr.id_string() + floatbv_suffix(expr));

    if(bvfp_set.insert(function).second)
    {
      out << "; this is a model for " << expr.id() << " : "
          << type2id(to_multi_ary_expr(expr).op0().type()) << " -> "
          << type2id(expr.type()) << "\n"
          << "(define-fun " << function << " (";

      for(std::size_t i = 0; i < expr.operands().size(); i++)
      {
        if(i!=0)
          out << " ";
        out << "(op" << i << ' ';
        convert_type(expr.operands()[i].type());
        out << ')';
      }

      out << ") ";
      convert_type(expr.type()); // return type
      out << ' ';

      exprt tmp1=expr;
      for(std::size_t i = 0; i < tmp1.operands().size(); i++)
        tmp1.operands()[i]=
          smt2_symbolt("op"+std::to_string(i), tmp1.operands()[i].type());

      exprt tmp2=float_bv(tmp1);
      tmp2=letify(tmp2);
      CHECK_RETURN(!tmp2.is_nil());

      convert_expr(tmp2);

      out << ")\n"; // define-fun
    }
  }
  else if(
    use_FPA_theory && expr.id() == ID_typecast &&
    to_typecast_expr(expr).op().type().id() == ID_floatbv &&
    expr.type().id() == ID_bv)
  {
    // This is _NOT_ a semantic conversion, but bit-wise.
    if(defined_expressions.find(expr) == defined_expressions.end())
    {
      // This conversion is non-trivial as it requires creating a
      // new bit-vector variable and then asserting that it converts
      // to the required floating-point number.
      const irep_idt id =
        "bvfromfloat." + std::to_string(defined_expressions.size());
      out << "(declare-fun " << id << " () ";
      convert_type(expr.type());
      out << ')' << '\n';

      const typecast_exprt &tc = to_typecast_expr(expr);
      const auto &floatbv_type = to_floatbv_type(tc.op().type());
      out << "(assert (= ";
      out << "((_ to_fp " << floatbv_type.get_e() << " "
          << floatbv_type.get_f() + 1 << ") " << id << ')';
      convert_expr(tc.op());
      out << ')'; // =
      out << ')' << '\n';

      defined_expressions[expr] = id;
    }
  }
  else if(expr.id() == ID_initial_state)
  {
    irep_idt function = "initial-state";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_unary_expr(expr).op().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_evaluate)
  {
    irep_idt function = "evaluate-" + type2id(expr.type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(
    expr.id() == ID_state_is_cstring ||
    expr.id() == ID_state_is_dynamic_object ||
    expr.id() == ID_state_live_object || expr.id() == ID_state_writeable_object)
  {
    irep_idt function =
      expr.id() == ID_state_is_cstring          ? "state-is-cstring"
      : expr.id() == ID_state_is_dynamic_object ? "state-is-dynamic-object"
      : expr.id() == ID_state_live_object       ? "state-live-object"
                                                : "state-writeable-object";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(
    expr.id() == ID_state_r_ok || expr.id() == ID_state_w_ok ||
    expr.id() == ID_state_rw_ok)
  {
    irep_idt function = expr.id() == ID_state_r_ok   ? "state-r-ok"
                        : expr.id() == ID_state_w_ok ? "state-w-ok"
                                                     : "state-rw-ok";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_ternary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_ternary_expr(expr).op1().type());
      out << ' ';
      convert_type(to_ternary_expr(expr).op2().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_update_state)
  {
    irep_idt function =
      "update-state-" + type2id(to_multi_ary_expr(expr).op2().type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_multi_ary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_multi_ary_expr(expr).op1().type());
      out << ' ';
      convert_type(to_multi_ary_expr(expr).op2().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_enter_scope_state)
  {
    irep_idt function =
      "enter-scope-state-" + type2id(to_binary_expr(expr).op1().type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ' ';
      convert_type(size_type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_exit_scope_state)
  {
    irep_idt function =
      "exit-scope-state-" + type2id(to_binary_expr(expr).op1().type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_allocate)
  {
    irep_idt function = "allocate";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_reallocate)
  {
    irep_idt function = "reallocate";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_ternary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_ternary_expr(expr).op1().type());
      out << ' ';
      convert_type(to_ternary_expr(expr).op2().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_deallocate_state)
  {
    irep_idt function = "deallocate";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_binary_expr(expr).op0().type());
      out << ' ';
      convert_type(to_binary_expr(expr).op1().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_object_address)
  {
    irep_idt function = "object-address";

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (String) ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_field_address)
  {
    irep_idt function = "field-address-" + type2id(expr.type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_field_address_expr(expr).op().type());
      out << ' ';
      out << "String";
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
  else if(expr.id() == ID_element_address)
  {
    irep_idt function = "element-address-" + type2id(expr.type());

    if(state_fkt_declared.insert(function).second)
    {
      out << "(declare-fun " << function << " (";
      convert_type(to_element_address_expr(expr).base().type());
      out << ' ';
      convert_type(to_element_address_expr(expr).index().type());
      out << ' '; // repeat, for the element size
      convert_type(to_element_address_expr(expr).index().type());
      out << ") ";
      convert_type(expr.type()); // return type
      out << ")\n";              // declare-fun
    }
  }
}

bool smt2_convt::use_array_theory(const exprt &expr)
{
  const typet &type = expr.type();
  PRECONDITION(type.id()==ID_array);

  // arrays inside structs get flattened, unless we have datatypes
  if(expr.id() == ID_with)
    return use_array_theory(to_with_expr(expr).old());
  else
    return use_datatypes || expr.id() != ID_member;
}

void smt2_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    CHECK_RETURN(array_type.size().is_not_nil());

    // we always use array theory for top-level arrays
    const typet &subtype = array_type.element_type();

    // Arrays map the index type to the element type.
    out << "(Array ";
    convert_type(array_type.index_type());
    out << " ";

    if(subtype.id()==ID_bool && !use_array_of_bool)
      out << "(_ BitVec 1)";
    else
      convert_type(array_type.element_type());

    out << ")";
  }
  else if(type.id()==ID_bool)
  {
    out << "Bool";
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(use_datatypes)
    {
      out << datatype_map.at(type);
    }
    else
    {
      std::size_t width=boolbv_width(type);

      out << "(_ BitVec " << width << ")";
    }
  }
  else if(type.id()==ID_code)
  {
    // These may appear in structs.
    // We replace this by "Bool" in order to keep the same
    // member count.
    out << "Bool";
  }
  else if(type.id() == ID_union || type.id() == ID_union_tag)
  {
    std::size_t width=boolbv_width(type);
    CHECK_RETURN_WITH_DIAGNOSTICS(
      to_union_type(ns.follow(type)).components().empty() || width != 0,
      "failed to get width of union");

    out << "(_ BitVec " << width << ")";
  }
  else if(type.id()==ID_pointer)
  {
    out << "(_ BitVec "
        << boolbv_width(type) << ")";
  }
  else if(type.id()==ID_bv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_bool)
  {
    out << "(_ BitVec "
        << to_bitvector_type(type).get_width() << ")";
  }
  else if(type.id()==ID_c_enum)
  {
    // these have an underlying type
    out << "(_ BitVec "
        << to_bitvector_type(to_c_enum_type(type).underlying_type()).get_width()
        << ")";
  }
  else if(type.id()==ID_c_enum_tag)
  {
    convert_type(ns.follow_tag(to_c_enum_tag_type(type)));
  }
  else if(type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(type);

    if(use_FPA_theory)
      out << "(_ FloatingPoint "
          << floatbv_type.get_e() << " "
          << floatbv_type.get_f() + 1 << ")";
    else
      out << "(_ BitVec "
          << floatbv_type.get_width() << ")";
  }
  else if(type.id()==ID_rational ||
          type.id()==ID_real)
    out << "Real";
  else if(type.id()==ID_integer)
    out << "Int";
  else if(type.id()==ID_complex)
  {
    if(use_datatypes)
    {
      out << datatype_map.at(type);
    }
    else
    {
      std::size_t width=boolbv_width(type);

      out << "(_ BitVec " << width << ")";
    }
  }
  else if(type.id()==ID_c_bit_field)
  {
    convert_type(c_bit_field_replacement_type(to_c_bit_field_type(type), ns));
  }
  else if(type.id() == ID_state)
  {
    out << "state";
  }
  else
  {
    UNEXPECTEDCASE("unsupported type: "+type.id_string());
  }
}

void smt2_convt::find_symbols(const typet &type)
{
  std::set<irep_idt> recstack;
  find_symbols_rec(type, recstack);
}

void smt2_convt::find_symbols_rec(
  const typet &type,
  std::set<irep_idt> &recstack)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    find_symbols(array_type.size());
    find_symbols_rec(array_type.element_type(), recstack);
  }
  else if(type.id()==ID_complex)
  {
    find_symbols_rec(to_complex_type(type).subtype(), recstack);

    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const std::string smt_typename =
        "complex." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;

      out << "(declare-datatypes ((" << smt_typename << " 0)) "
          << "(((mk-" << smt_typename;

      out << " (" << smt_typename << ".imag ";
      convert_type(to_complex_type(type).subtype());
      out << ")";

      out << " (" << smt_typename << ".real ";
      convert_type(to_complex_type(type).subtype());
      out << ")";

      out << "))))\n";
    }
  }
  else if(type.id() == ID_struct)
  {
    // Cater for mutually recursive struct types
    bool need_decl=false;
    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const std::string smt_typename =
        "struct." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;
      need_decl=true;
    }

    const struct_typet::componentst &components =
      to_struct_type(type).components();

    for(const auto &component : components)
      find_symbols_rec(component.type(), recstack);

    // Declare the corresponding SMT type if we haven't already.
    if(need_decl)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // We're going to create a datatype named something like `struct.0'.
      // It's going to have a single constructor named `mk-struct.0' with an
      // argument for each member of the struct.  The declaration that
      // creates this type looks like:
      //
      // (declare-datatypes ((struct.0 0)) (((mk-struct.0
      //                                   (struct.0.component1 type1)
      //                                   ...
      //                                   (struct.0.componentN typeN)))))
      out << "(declare-datatypes ((" << smt_typename << " 0)) "
          << "(((mk-" << smt_typename << " ";

      for(const auto &component : components)
      {
        if(is_zero_width(component.type(), ns))
          continue;

        out << "(" << smt_typename << "." << component.get_name()
                      << " ";
        convert_type(component.type());
        out << ") ";
      }

      out << "))))" << "\n";

      // Let's also declare convenience functions to update individual
      // members of the struct whil we're at it.  The functions are
      // named like `update-struct.0.component1'.  Their declarations
      // look like:
      //
      // (declare-fun update-struct.0.component1
      //         ((s struct.0)     ; first arg -- the struct to update
      //          (v type1))       ; second arg -- the value to update
      //         struct.0          ; the output type
      //         (mk-struct.0      ; build the new struct...
      //          v                ; the updated value
      //          (struct.0.component2 s)  ; retain the other members
      //          ...
      //          (struct.0.componentN s)))

      for(struct_union_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          ++it)
      {
        if(is_zero_width(it->type(), ns))
          continue;

        const struct_union_typet::componentt &component=*it;
        out << "(define-fun update-" << smt_typename << "."
            << component.get_name() << " "
            << "((s " << smt_typename << ") "
            <<  "(v ";
        convert_type(component.type());
        out << ")) " << smt_typename << " "
            << "(mk-" << smt_typename
            << " ";

        for(struct_union_typet::componentst::const_iterator
            it2=components.begin();
            it2!=components.end();
            ++it2)
        {
          if(it==it2)
            out << "v ";
          else if(!is_zero_width(it2->type(), ns))
          {
            out << "(" << smt_typename << "."
                << it2->get_name() << " s) ";
          }
        }

        out << "))" << "\n";
      }

      out << "\n";
    }
  }
  else if(type.id() == ID_union)
  {
    const union_typet::componentst &components =
      to_union_type(type).components();

    for(const auto &component : components)
      find_symbols_rec(component.type(), recstack);
  }
  else if(type.id()==ID_code)
  {
    const code_typet::parameterst &parameters=
      to_code_type(type).parameters();
    for(const auto &param : parameters)
      find_symbols_rec(param.type(), recstack);

    find_symbols_rec(to_code_type(type).return_type(), recstack);
  }
  else if(type.id()==ID_pointer)
  {
    find_symbols_rec(to_pointer_type(type).base_type(), recstack);
  }
  else if(type.id() == ID_struct_tag)
  {
    const auto &struct_tag = to_struct_tag_type(type);
    const irep_idt &id = struct_tag.get_identifier();

    if(recstack.find(id) == recstack.end())
    {
      const auto &base_struct = ns.follow_tag(struct_tag);
      recstack.insert(id);
      find_symbols_rec(base_struct, recstack);
      datatype_map[type] = datatype_map[base_struct];
    }
  }
  else if(type.id() == ID_union_tag)
  {
    const auto &union_tag = to_union_tag_type(type);
    const irep_idt &id = union_tag.get_identifier();

    if(recstack.find(id) == recstack.end())
    {
      recstack.insert(id);
      find_symbols_rec(ns.follow_tag(union_tag), recstack);
    }
  }
  else if(type.id() == ID_state)
  {
    if(datatype_map.find(type) == datatype_map.end())
    {
      datatype_map[type] = "state";
      out << "(declare-sort state 0)\n";
    }
  }
  else if(type.id() == ID_mathematical_function)
  {
    const auto &mathematical_function_type =
      to_mathematical_function_type(type);
    for(auto &d_type : mathematical_function_type.domain())
      find_symbols_rec(d_type, recstack);

    find_symbols_rec(mathematical_function_type.codomain(), recstack);
  }
}

std::size_t smt2_convt::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}
