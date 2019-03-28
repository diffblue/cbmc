/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SMT Backend

#include "smt2_conv.h"
#include "smt2_ast.h"
#include "smt2_command.h"
#include "smt2_util.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/fixedbv.h>
#include <util/format_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string2int.h>
#include <util/string_constant.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>
#include <solvers/lowering/expr_lowering.h>
#include <solvers/prop/literal_expr.h>
#include <util/make_unique.h>

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
    use_datatypes(false),
    use_array_of_bool(false),
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

  case solvert::BOOLECTOR:
    break;

  case solvert::CPROVER_SMT2:
    use_array_of_bool = true;
    emit_set_logic = false;
    break;

  case solvert::CVC3:
    break;

  case solvert::CVC4:
    break;

  case solvert::MATHSAT:
    break;

  case solvert::YICES:
    break;

  case solvert::Z3:
    use_array_of_bool = true;
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
  case solvert::BOOLECTOR: out << "; Generated for Boolector\n"; break;
  case solvert::CPROVER_SMT2:
    out << "; Generated for the CPROVER SMT2 solver\n"; break;
  case solvert::CVC3: out << "; Generated for CVC 3\n"; break;
  case solvert::CVC4: out << "; Generated for CVC 4\n"; break;
  case solvert::MATHSAT: out << "; Generated for MathSAT\n"; break;
  case solvert::YICES: out << "; Generated for Yices\n"; break;
  case solvert::Z3: out << "; Generated for Z3\n"; break;
    // clang-format on
  }

  out << smt2_commandt::set_info(
           smt2_symbolt{":source"}, smt2_string_literalt(notes))
      << smt2_commandt::set_option(
           smt2_symbolt{":produce-models"}, smt2_symbolt{"true"});

  // We use a broad mixture of logics, so on some solvers
  // its better not to declare here.
  // set-logic should come after setting options
  if(emit_set_logic && !logic.empty())
    out << smt2_commandt::set_logic(smt2_symbolt{logic});
}

void smt2_convt::write_footer(std::ostream &os)
{
  os << "\n";

  // add the assumptions, if any
  if(!assumptions.empty())
  {
    os << "; assumptions\n";

    for(const auto &assumption : assumptions)
    {
      os << smt2_commandt::_assert(
        convert_literal(to_literal_expr(assumption).get_literal()));
    }
  }

  // fix up the object sizes
  for(const auto &object : object_sizes)
    define_object_size(object.second, object.first);

  os << smt2_commandt::check_sat();
  os << "\n";

  if(solver!=solvert::BOOLECTOR)
  {
    for(const auto &id : smt2_identifiers)
    {
      os << smt2_commandt::get_value(
        smt2_listt<smt2_astt>{{smt2_symbolt{"|" + id + "|"}}});
    }
  }

  os << "\n";

  os << smt2_commandt::exit();

  os << "; end of SMT2 file"
     << "\n";
}

void smt2_convt::define_object_size(
  const irep_idt &id,
  const exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_size);
  const exprt &ptr = expr.op0();
  std::size_t size_width = boolbv_width(expr.type());
  std::size_t pointer_width = boolbv_width(ptr.type());
  std::size_t number = 0;
  std::size_t h=pointer_width-1;
  std::size_t l=pointer_width-config.bv_encoding.object_bits;

  for(const auto &o : pointer_logic.objects)
  {
    const typet &type = o.type();
    auto size_expr = size_of_expr(type, ns);
    const auto object_size =
      numeric_cast<mp_integer>(size_expr.value_or(nil_exprt()));

    if(
      o.id() != ID_symbol || !size_expr.has_value() || !object_size.has_value())
    {
      ++number;
      continue;
    }

    // (assert (implies (= ((_ extract h l) ptr) (_ bv number
    // config.bv_encoding.object_bits)) (= id (_ bv object_size size_width))))
    out << smt2_commandt::_assert(smt2_implies(
      smt2_eq(
        smt2_function_applicationt(smt2_extract(h, l), {convert_expr(ptr)}),
        smt2_bv(number, config.bv_encoding.object_bits)),
      smt2_eq(smt2_symbolt{id}, smt2_bv(*object_size, size_width))));

    ++number;
  }
}

decision_proceduret::resultt smt2_convt::dec_solve()
{
  write_footer(out);
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
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id=to_nondet_symbol_expr(expr).get_identifier();

    identifier_mapt::const_iterator it=identifier_map.find(id);

    if(it!=identifier_map.end())
      return it->second.value;
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    exprt tmp=get(member_expr.struct_op());
    if(tmp.is_nil())
      return nil_exprt();
    return member_exprt(tmp, member_expr.get_component_name(), expr.type());
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
  else if(expr.is_constant())
    return expr;

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
    return ieee_floatt::plus_infinity(ieee_float_spect(s, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="-oo") // (_ -oo e s)
  {
    std::size_t e = unsafe_string2size_t(src.get_sub()[2].id_string());
    std::size_t s = unsafe_string2size_t(src.get_sub()[3].id_string());
    return ieee_floatt::minus_infinity(ieee_float_spect(s, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="NaN") // (_ NaN e s)
  {
    std::size_t e = unsafe_string2size_t(src.get_sub()[2].id_string());
    std::size_t s = unsafe_string2size_t(src.get_sub()[3].id_string());
    return ieee_floatt::NaN(ieee_float_spect(s, e)).to_expr();
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
    INVARIANT(
      false,
      "smt2_convt::parse_literal should not be of unsupported type " +
        type.id_string());
}

exprt smt2_convt::parse_array(
  const irept &src,
  const array_typet &type)
{
  if(src.get_sub().size()==4 && src.get_sub()[0].id()=="store")
  {
    // (store array index value)
    if(src.get_sub().size()!=4)
      return nil_exprt();

    exprt array=parse_array(src.get_sub()[1], type);
    exprt index=parse_rec(src.get_sub()[2], type.size().type());
    exprt value=parse_rec(src.get_sub()[3], type.subtype());

    return with_exprt(array, index, value);
  }
  else if(src.get_sub().size()==2 &&
          src.get_sub()[0].get_sub().size()==3 &&
          src.get_sub()[0].get_sub()[0].id()=="as" &&
          src.get_sub()[0].get_sub()[1].id()=="const")
  {
    // This is produced by Z3.
    // ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
    exprt value=parse_rec(src.get_sub()[1], type.subtype());
    return array_of_exprt(value, type);
  }
  else
    return nil_exprt();
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

    if(src.get_sub().size()!=components.size()+1)
      return result; // give up

    for(std::size_t i=0; i<components.size(); i++)
    {
      const struct_typet::componentt &c=components[i];
      result.operands()[i]=parse_rec(src.get_sub()[i+1], c.type());
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
  if(
    type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
    type.id() == ID_integer || type.id() == ID_rational ||
    type.id() == ID_real || type.id() == ID_c_enum ||
    type.id() == ID_c_enum_tag || type.id() == ID_fixedbv ||
    type.id() == ID_floatbv)
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
    pointer_logict::pointert ptr;
    ptr.object = numeric_cast_v<std::size_t>(v / pow);
    ptr.offset=v%pow;
    return pointer_logic.pointer_expr(ptr, to_pointer_type(type));
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

smt2_astt smt2_convt::convert_address_of_rec(
  const exprt &expr,
  const pointer_typet &result_type)
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_constant ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_label)
  {
    return smt2_concat(
      smt2_bv(pointer_logic.add_object(expr), config.bv_encoding.object_bits),
      smt2_bv(0, boolbv_width(result_type) - config.bv_encoding.object_bits));
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);

    const exprt &array = index_expr.array();
    const exprt &index = index_expr.index();

    if(index.is_zero())
    {
      if(array.type().id()==ID_pointer)
        return convert_expr(array);
      else if(array.type().id()==ID_array)
        return convert_address_of_rec(array, result_type);
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
        pointer_type(array.type().subtype()));

      plus_exprt plus_expr{address_of_expr, index};

      return convert_expr(plus_expr);
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
    return smt2_bvadd(
      convert_address_of_rec(struct_op, result_type),
      convert_expr(from_integer(*offset, index_type)));
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);
    return smt2_ite(
      convert_expr(if_expr.cond()),
      convert_address_of_rec(if_expr.true_case(), result_type),
      convert_address_of_rec(if_expr.false_case(), result_type));
  }
  else
    INVARIANT(
      false,
      "operand of address of expression should not be of kind " +
        expr.id_string());
}

/// Create a name for the literal with the given number, add it to the set of
/// identifiers and return a corresponding symbolt
static smt2_symbolt
literal_name(literalt::var_not var_no, std::set<std::string> &smt2_identifiers)
{
  std::string literal_name = "B" + std::to_string(var_no);
  smt2_identifiers.insert(literal_name);
  return smt2_symbolt("|" + literal_name + "|");
}

literalt smt2_convt::convert(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  // Three cases where no new handle is needed.

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);
  else if(expr.id()==ID_literal)
    return to_literal_expr(expr).get_literal();

  // Need a new handle

  out << "\n";

  auto prepared_expr_with_dependencies = prepare_for_convert_expr(expr);
  for(const auto &command : prepared_expr_with_dependencies.first)
    out << *command;

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;

  out << "; convert\n";

  // (define-fun l () Bool expr)
  out << smt2_commandt::define_fun(
    literal_name(l.var_no(), smt2_identifiers),
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>>{{}},
    smt2_sortt::Bool(),
    convert_expr(prepared_expr_with_dependencies.second));

  return l;
}

exprt smt2_convt::handle(const exprt &expr)
{
  // We can only improve Booleans.
  if(expr.type().id() != ID_bool)
    return expr;

  return literal_exprt(convert(expr));
}

smt2_astt smt2_convt::convert_literal(const literalt l)
{
  if(l==const_literal(false))
    return smt2_symbolt("false");
  if(l == const_literal(true))
    return smt2_symbolt("true");

  auto literal_without_sign = literal_name(l.var_no(), smt2_identifiers);

  if(!l.sign())
    return std::move(literal_without_sign);
  return smt2_not(std::move(literal_without_sign));
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

std::string smt2_convt::convert_identifier(const irep_idt &identifier)
{
  // Backslashes are disallowed in quoted symbols just for simplicity.
  // Otherwise, for Common Lisp compatibility they would have to be treated
  // as escaping symbols.

  std::string result;

  for(std::size_t i=0; i<identifier.size(); i++)
  {
    char ch=identifier[i];

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

  return result;
}

std::string smt2_convt::type2id(const typet &type) const
{
  if(type.id()==ID_floatbv)
  {
    ieee_float_spect spec(to_floatbv_type(type));
    return "f"+std::to_string(spec.width())+"_"+std::to_string(spec.f);
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
    return type2id(ns.follow_tag(to_c_enum_tag_type(type)).subtype());
  }
  else if(type.id() == ID_pointer)
  {
    return "p" + std::to_string(to_pointer_type(type).get_width());
  }
  else
  {
    UNREACHABLE;
  }
}

std::string smt2_convt::floatbv_suffix(const exprt &expr) const
{
  PRECONDITION(!expr.operands().empty());
  return "_"+type2id(expr.op0().type())+"->"+type2id(expr.type());
}

smt2_astt smt2_convt::convert_floatbv(const exprt &expr)
{
  PRECONDITION(!use_FPA_theory);

  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    return smt2_symbolt("|" + convert_identifier(id) + '|');
  }

  if(expr.id()==ID_smt2_symbol)
  {
    const irep_idt &id = to_smt2_symbol(expr).get_identifier();
    return smt2_symbolt(id2string(id));
  }

  INVARIANT(
    !expr.operands().empty(), "non-symbol expressions shall have operands");

  smt2_symbolt quoted_symbol{"|float_bv." + id2string(expr.id()) +
                             floatbv_suffix(expr) + '|'};
  smt2_function_applicationt node{smt2_identifiert{std::move(quoted_symbol)},
                                  {}};

  forall_operands(it, expr)
    node.add_argument(convert_expr(*it));

  return std::move(node);
}

smt2_astt smt2_convt::convert_expr(const exprt &expr)
{
  // huge monster case split over expression id
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "symbol must have identifier");
    return smt2_symbolt("|" + convert_identifier(id) + '|');
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id = to_nondet_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "nondet symbol must have identifier");
    return smt2_symbolt(
      "|" + convert_identifier("nondet_" + id2string(id)) + "|");
  }
  else if(expr.id()==ID_smt2_symbol)
  {
    const irep_idt &id = to_smt2_symbol(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "smt2 symbol must have identifier");
    return smt2_symbolt(id2string(id));
  }
  else if(expr.id()==ID_typecast)
  {
    return convert_typecast(to_typecast_expr(expr));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  else if(expr.id()==ID_struct)
  {
    return convert_struct(to_struct_expr(expr));
  }
  else if(expr.id()==ID_union)
  {
    return convert_union(to_union_expr(expr));
  }
  else if(expr.id()==ID_constant)
  {
    return convert_constant(to_constant_expr(expr));
  }
  else if(expr.id() == ID_concatenation && expr.operands().size() == 1)
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      expr.type() == expr.operands().front().type(),
      "concatenation over a single operand should have matching types",
      expr.pretty());

    return convert_expr(expr.operands().front());
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

    auto function_name = smt2_symbolt([&] {
      if(expr.id() == ID_concatenation)
        return "concat";
      else if(expr.id() == ID_bitand)
        return "bvand";
      else if(expr.id() == ID_bitor)
        return "bvor";
      else if(expr.id() == ID_bitxor)
        return "bvxor";
      else if(expr.id() == ID_bitnand)
        return "bvnand";
      else if(expr.id() == ID_bitnor)
        return "bvnor";
      UNREACHABLE;
    }());

    smt2_function_applicationt application{
      smt2_identifiert{std::move(function_name)}, {}};
    for(const exprt &e : expr.operands())
      application.add_argument(flatten2bv(e));
    return std::move(application);
  }
  else if(expr.id()==ID_bitnot)
  {
    const bitnot_exprt &bitnot_expr = to_bitnot_expr(expr);

    if(bitnot_expr.type().id() == ID_vector)
    {
      if(use_datatypes)
      {
        const std::string &smt_typename = datatype_map.at(bitnot_expr.type());

        // extract elements
        const vector_typet &vector_type = to_vector_type(bitnot_expr.type());

        mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());
        typet index_type=vector_type.size().type();

        smt2_function_applicationt bvnot_node{
          smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}}, {}};

        // do bitnot component-by-component
        for(mp_integer i=0; i!=size; ++i)
        {
          smt2_symbolt function_name{smt_typename + "." +
                                     std::to_string((size - i - 1).to_long())};
          bvnot_node.add_argument(smt2_bvnot(smt2_function_applicationt{
            smt2_identifiert{std::move(function_name)},
            {smt2_symbolt{"?vectorop"}}}));
        }

        return smt2_lett{
          smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
            {smt2_pairt<smt2_symbolt, smt2_astt>{
              smt2_symbolt{"?vectorop"}, convert_expr(bitnot_expr.op())}}},
          std::move(bvnot_node)};
      }
      else
        SMT2_TODO("bitnot for vectors");
    }
    else
    {
      return smt2_bvnot(convert_expr(bitnot_expr.op()));
    }
  }
  else if(expr.id()==ID_unary_minus)
  {
    const unary_minus_exprt &unary_minus_expr = to_unary_minus_expr(expr);

    if(
      unary_minus_expr.type().id() == ID_rational ||
      unary_minus_expr.type().id() == ID_integer ||
      unary_minus_expr.type().id() == ID_real)
    {
      return smt2_function_applicationt{smt2_identifiert{smt2_symbolt{"-"}},
                                        {convert_expr(unary_minus_expr.op())}};
    }
    else if(unary_minus_expr.type().id() == ID_floatbv)
    {
      // this has no rounding mode
      if(use_FPA_theory)
      {
        return smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt{"fp.neg"}},
          {convert_expr(unary_minus_expr.op())}};
      }
      else
        return convert_floatbv(unary_minus_expr);
    }
    else if(unary_minus_expr.type().id() == ID_vector)
    {
      if(use_datatypes)
      {
        const std::string &smt_typename =
          datatype_map.at(unary_minus_expr.type());

        // extract elements
        const vector_typet &vector_type =
          to_vector_type(unary_minus_expr.type());

        mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

        auto bvneg_node = smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}}, {}};
        typet index_type=vector_type.size().type();

        // negate component-by-component
        for(mp_integer i=0; i!=size; ++i)
        {
          smt2_symbolt function_name{smt_typename + "." +
                                     std::to_string((size - i - 1).to_long())};
          bvneg_node.add_argument(smt2_bvneg(smt2_function_applicationt{
            smt2_identifiert{std::move(function_name)},
            {smt2_symbolt{"?vectorop"}}}));
        }

        return smt2_lett{
          smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
            {smt2_pairt<smt2_symbolt, smt2_astt>{
              smt2_symbolt{"?vectorop"}, convert_expr(unary_minus_expr.op())}}},
          std::move(bvneg_node)};
      }
      else
        SMT2_TODO("unary minus for vector");
    }
    else
    {
      return smt2_bvneg(convert_expr(unary_minus_expr.op()));
    }
  }
  else if(expr.id()==ID_unary_plus)
  {
    // A no-op (apart from type promotion)
    return convert_expr(to_unary_plus_expr(expr).op());
  }
  else if(expr.id()==ID_sign)
  {
    const sign_exprt &sign_expr = to_sign_expr(expr);

    const typet &op_type = sign_expr.op().type();

    if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        return smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt{"fp.isNegative"}},
          {convert_expr(sign_expr.op())}};
      }
      else
        return convert_floatbv(sign_expr);
    }
    else if(op_type.id()==ID_signedbv)
    {
      std::size_t op_width=to_signedbv_type(op_type).get_width();
      return smt2_bvslt(convert_expr(sign_expr.op()), smt2_bv(0, op_width));
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
    return smt2_ite(
      convert_expr(if_expr.cond()),
      convert_expr(if_expr.true_case()),
      convert_expr(if_expr.false_case()));
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.type().id() == ID_bool,
      "logical and, or, and xor expressions should have Boolean type");
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions should have at least two operands");

    auto node =
      smt2_function_applicationt{smt2_identifiert{smt2_symbolt{expr.id()}}, {}};
    forall_operands(it, expr)
      node.add_argument(convert_expr(*it));
    return std::move(node);
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);

    DATA_INVARIANT(
      implies_expr.type().id() == ID_bool,
      "implies expression should have Boolean type");

    return smt2_implies(
      convert_expr(implies_expr.op0()), convert_expr(implies_expr.op1()));
  }
  else if(expr.id()==ID_not)
  {
    const not_exprt &not_expr = to_not_expr(expr);

    DATA_INVARIANT(
      not_expr.type().id() == ID_bool,
      "not expression should have Boolean type");

    return smt2_not(convert_expr(not_expr.op()));
  }
  else if(expr.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(expr);

    DATA_INVARIANT(
      equal_expr.op0().type() == equal_expr.op1().type(),
      "operands of equal expression shall have same type");

    return smt2_eq(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if(expr.id() == ID_notequal)
  {
    const notequal_exprt &notequal_expr = to_notequal_expr(expr);

    DATA_INVARIANT(
      notequal_expr.op0().type() == notequal_expr.op1().type(),
      "operands of not equal expression shall have same type");

    return smt2_not(smt2_eq(
      convert_expr(notequal_expr.op0()), convert_expr(notequal_expr.op1())));
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    // These are not the same as (= A B)
    // because of NaN and negative zero.
    DATA_INVARIANT(
      expr.operands().size() == 2,
      "float equal and not equal expressions must have two operands");
    DATA_INVARIANT(
      expr.op0().type() == expr.op1().type(),
      "operands of float equal and not equal expressions shall have same type");

    // The FPA theory properly treats NaN and negative zero.
    if(use_FPA_theory)
    {
      smt2_function_applicationt node{
        smt2_identifiert{smt2_symbolt{"fp.eq"}},
        {convert_expr(expr.op0()), convert_expr(expr.op1())}};
      if(expr.id()==ID_ieee_float_notequal)
        return smt2_not(std::move(node));
      return std::move(node);
    }
    else
      return convert_floatbv(expr);
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    return convert_relation(expr);
  }
  else if(expr.id()==ID_plus)
  {
    return convert_plus(to_plus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_plus)
  {
    return convert_floatbv_plus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_minus)
  {
    return convert_minus(to_minus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_minus)
  {
    return convert_floatbv_minus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_div)
  {
    return convert_div(to_div_expr(expr));
  }
  else if(expr.id()==ID_floatbv_div)
  {
    return convert_floatbv_div(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_mod)
  {
    return convert_mod(to_mod_expr(expr));
  }
  else if(expr.id()==ID_mult)
  {
    return convert_mult(to_mult_expr(expr));
  }
  else if(expr.id()==ID_floatbv_mult)
  {
    return convert_floatbv_mult(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr = to_address_of_expr(expr);
    return convert_address_of_rec(
      address_of_expr.object(), to_pointer_type(address_of_expr.type()));
  }
  else if(expr.id()==ID_array_of)
  {
    const array_of_exprt &array_of_expr = to_array_of_expr(expr);

    DATA_INVARIANT(
      array_of_expr.type().id() == ID_array,
      "array of expression shall have array type");

    defined_expressionst::const_iterator it =
      defined_expressions.find(array_of_expr);
    CHECK_RETURN(it != defined_expressions.end());
    return smt2_symbolt(id2string(it->second));
  }
  else if(expr.id()==ID_index)
  {
    return convert_index(to_index_expr(expr));
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
      auto function_name = smt2_symbolt([&] {
        if(shift_expr.id() == ID_ashr)
          return "bvashr";
        else if(shift_expr.id() == ID_lshr)
          return "bvlshr";
        else if(shift_expr.id() == ID_shl)
          return "bvshl";
        else
          UNREACHABLE;
      }());
      smt2_function_applicationt application{smt2_identifiert{function_name},
                                             {}};
      application.add_argument(convert_expr(shift_expr.op()));

      // SMT2 requires the shift distance to have the same width as
      // the value that is shifted -- odd!

      auto child = [&]() -> smt2_astt {
        if(shift_expr.distance().type().id() == ID_integer)
        {
          const mp_integer i =
            numeric_cast_v<mp_integer>(to_constant_expr(shift_expr.distance()));

          // shift distance must be bit vector
          std::size_t width_op0 = boolbv_width(shift_expr.op().type());
          exprt tmp = from_integer(i, unsignedbv_typet(width_op0));
          return convert_expr(tmp);
        }
        else if(
          shift_expr.distance().type().id() == ID_signedbv ||
          shift_expr.distance().type().id() == ID_unsignedbv ||
          shift_expr.distance().type().id() == ID_c_enum ||
          shift_expr.distance().type().id() == ID_c_bool)
        {
          std::size_t width_op0 = boolbv_width(shift_expr.op().type());
          std::size_t width_op1 = boolbv_width(shift_expr.distance().type());

          if(width_op0 == width_op1)
            return convert_expr(shift_expr.distance());
          else if(width_op0 > width_op1)
          {
            return smt2_function_applicationt{
              smt2_zero_extend(width_op0 - width_op1),
              {convert_expr(shift_expr.distance())}};
          }
          else // width_op0<width_op1
          {
            return smt2_function_applicationt{
              smt2_extract(width_op0 - 1, 0),
              {convert_expr(shift_expr.distance())}};
          }
        }
        else
          UNEXPECTEDCASE(
            "unsupported distance type for " + shift_expr.id_string() + ": " +
            type.id_string());
      }();
      application.add_argument(std::move(child));
      return std::move(application);
    }
    else
      UNEXPECTEDCASE(
        "unsupported type for " + shift_expr.id_string() + ": " +
        type.id_string());
  }
  else if(expr.id()==ID_with)
  {
    return convert_with(to_with_expr(expr));
  }
  else if(expr.id()==ID_update)
  {
    return convert_update(expr);
  }
  else if(expr.id()==ID_member)
  {
    return convert_member(to_member_expr(expr));
  }
  else if(expr.id()==ID_pointer_offset)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1,
      "pointer offset expression shall have one operand");
    DATA_INVARIANT(
      expr.op0().type().id() == ID_pointer,
      "operand of pointer offset expression shall be of pointer type");

    std::size_t offset_bits=
      boolbv_width(expr.op0().type())-config.bv_encoding.object_bits;
    std::size_t result_width=boolbv_width(expr.type());

    // max extract width
    if(offset_bits>result_width)
      offset_bits=result_width;

    smt2_function_applicationt application{smt2_extract(offset_bits - 1, 0),
                                           {convert_expr(expr.op0())}};

    // too few bits?
    if(result_width>offset_bits)
    {
      return smt2_function_applicationt{
        smt2_zero_extend(result_width - offset_bits), {std::move(application)}};
    }
    return std::move(application);
  }
  else if(expr.id()==ID_pointer_object)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1,
      "pointer object expressions should have one operand");

    DATA_INVARIANT(
      expr.op0().type().id() == ID_pointer,
      "pointer object expressions should be of pointer type");

    std::size_t ext=boolbv_width(expr.type())-config.bv_encoding.object_bits;
    std::size_t pointer_width=boolbv_width(expr.op0().type());

    smt2_function_applicationt node{
      smt2_extract(
        pointer_width - 1, pointer_width - config.bv_encoding.object_bits),
      {convert_expr(expr.op0())}};

    if(ext <= 0)
      return std::move(node);
    return smt2_function_applicationt{smt2_zero_extend(ext), {std::move(node)}};
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    return convert_is_dynamic_object(expr);
  }
  else if(expr.id() == ID_is_invalid_pointer)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1,
      "invalid pointer expression shall have one operand");

    std::size_t pointer_width=boolbv_width(expr.op0().type());
    return smt2_eq(
      smt2_function_applicationt{
        smt2_extract(
          pointer_width - 1, pointer_width - config.bv_encoding.object_bits),
        {convert_expr(expr.op0())}},
      smt2_bv(
        pointer_logic.get_invalid_object(), config.bv_encoding.object_bits));
  }
  else if(expr.id()==ID_string_constant)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    return smt2_symbolt(it->second);
  }
  else if(expr.id()==ID_extractbit)
  {
    const extractbit_exprt &extractbit_expr = to_extractbit_expr(expr);

    if(extractbit_expr.index().is_constant())
    {
      const mp_integer i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbit_expr.index()));
      return smt2_eq(
        smt2_function_applicationt{smt2_extract(i, i),
                                   {flatten2bv(extractbit_expr.src())}},
        smt2_symbolt("#b1"));
    }
    else
    {
      typecast_exprt tmp(extractbit_expr.index(), extractbit_expr.src().type());
      return smt2_eq(
        smt2_function_applicationt{smt2_extract(0, 0),
                                   {smt2_symbolt{"bvlshr"},
                                    flatten2bv(extractbit_expr.src()),
                                    convert_expr(tmp)}},
        smt2_symbolt{"bin1"});
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
      return smt2_function_applicationt{smt2_extract(op1_i, op2_i),
                                        {flatten2bv(extractbits_expr.src())}};
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
    return smt2_function_applicationt{smt2_repeat(smt2_constantt::make(times)),
                                      {flatten2bv(replication_expr.op())}};
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
  else if(expr.id()==ID_width)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "width expression should have one operand");

    std::size_t result_width=boolbv_width(expr.type());
    CHECK_RETURN(result_width != 0);

    std::size_t op_width=boolbv_width(expr.op0().type());
    CHECK_RETURN(op_width != 0);

    return smt2_bv(op_width / 8, result_width);
  }
  else if(expr.id()==ID_abs)
  {
    const abs_exprt &abs_expr = to_abs_expr(expr);

    const typet &type = abs_expr.type();

    if(type.id()==ID_signedbv)
    {
      std::size_t result_width = to_signedbv_type(type).get_width();
      return smt2_ite(
        smt2_bvslt(convert_expr(abs_expr.op()), smt2_bv(0, result_width)),
        smt2_bvneg(convert_expr(abs_expr.op())),
        convert_expr(abs_expr.op()));
    }
    else if(type.id()==ID_fixedbv)
    {
      std::size_t result_width=to_fixedbv_type(type).get_width();
      return smt2_ite(
        smt2_bvslt(convert_expr(abs_expr.op()), smt2_bv(0, result_width)),
        smt2_bvneg(convert_expr(abs_expr.op())),
        convert_expr(abs_expr.op()));
    }
    else if(type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        return smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt{"fp.abs"}},
          {convert_expr(abs_expr.op())}};
      }
      else
        return convert_floatbv(abs_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnan)
  {
    const isnan_exprt &isnan_expr = to_isnan_expr(expr);

    const typet &op_type = isnan_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      return smt2_symbolt{"false"};
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
        return smt2_fp_is_nan(convert_expr(isnan_expr.op()));
      else
        return convert_floatbv(isnan_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isfinite)
  {
    const isfinite_exprt &isfinite_expr = to_isfinite_expr(expr);

    const typet &op_type = isfinite_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      return smt2_symbolt{"true"};
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        return smt2_and(
          smt2_not(smt2_fp_is_nan(convert_expr(isfinite_expr.op()))),
          smt2_not(smt2_fp_is_infinite(convert_expr(isfinite_expr.op()))));
      }
      else
        return convert_floatbv(isfinite_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isinf)
  {
    const isinf_exprt &isinf_expr = to_isinf_expr(expr);

    const typet &op_type = isinf_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      return smt2_symbolt("false");
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
        return smt2_fp_is_infinite(convert_expr(isinf_expr.op()));
      else
        return convert_floatbv(isinf_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnormal)
  {
    const isnormal_exprt &isnormal_expr = to_isnormal_expr(expr);

    const typet &op_type = isnormal_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      return smt2_symbolt{"true"};
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
        return smt2_fp_is_normal(convert_expr(isnormal_expr.op()));
      else
        return convert_floatbv(isnormal_expr);
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_overflow_plus ||
          expr.id()==ID_overflow_minus)
  {
    DATA_INVARIANT(
      expr.operands().size() == 2,
      "overflow plus and overflow minus expressions shall have two operands");

    DATA_INVARIANT(
      expr.type().id() == ID_bool,
      "overflow plus and overflow minus expressions shall be of Boolean type");

    bool subtract=expr.id()==ID_overflow_minus;
    const typet &op_type=expr.op0().type();
    std::size_t width=boolbv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      // an overflow occurs if the top two bits of the extended sum differ
      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{
            smt2_symbolt("?sum"),
            smt2_function_applicationt{
              smt2_identifiert{smt2_symbolt{subtract ? "bvsub" : "bvadd"}},
              {smt2_function_applicationt{
                 smt2_sign_extend(smt2_constantt::make(1)),
                 {convert_expr(expr.op0())}},
               smt2_function_applicationt{
                 smt2_sign_extend(smt2_constantt::make(1)),
                 {convert_expr(expr.op1())}}}},
          }}},
        smt2_not(smt2_eq(
          smt2_function_applicationt{smt2_extract(width, width),
                                     {smt2_symbolt{"?sum"}}},
          smt2_function_applicationt{smt2_extract(width - 1, width - 1),
                                     {smt2_symbolt{"?sum"}}})));
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_pointer)
    {
      // overflow is simply carry-out
      return smt2_eq(
        smt2_function_applicationt{
          smt2_extract(width, width),
          {smt2_function_applicationt{
            smt2_identifiert{smt2_symbolt{subtract ? "bvsub" : "bvadd"}},
            {smt2_function_applicationt{smt2_zero_extend(1),
                                        {convert_expr(expr.op0())}},
             smt2_function_applicationt{smt2_zero_extend(1),
                                        {convert_expr(expr.op1())}}}}}},
        smt2_symbolt{"#b1"});
    }
    else
    {
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "overflow check should not be performed on unsupported type",
        op_type.id_string());
    }
  }
  else if(expr.id()==ID_overflow_mult)
  {
    DATA_INVARIANT(
      expr.operands().size() == 2,
      "overflow mult expression shall have two operands");

    DATA_INVARIANT(
      expr.type().id() == ID_bool,
      "overflow mult expression shall be of Boolean type");

    // No better idea than to multiply with double the bits and then compare
    // with max value.

    const typet &op_type=expr.op0().type();
    std::size_t width=boolbv_width(op_type);

    if(op_type.id()==ID_signedbv)
    {
      return smt2_lett{
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{
            smt2_symbolt{"prod"},
            smt2_bvmul(
              smt2_function_applicationt{
                smt2_sign_extend(smt2_constantt::make(width)),
                {convert_expr(expr.op0())}},
              smt2_function_applicationt{
                smt2_sign_extend(smt2_constantt::make(width)),
                {convert_expr(expr.op1())}})}}},
        smt2_or(
          smt2_bvsge(
            smt2_symbolt("prod"), smt2_bv(power(2, width - 1), width * 2)),
          smt2_bvslt(
            smt2_symbolt("prod"),
            smt2_bvneg(smt2_bv(power(2, width - 1), width * 2))))};
    }
    else if(op_type.id()==ID_unsignedbv)
    {
      return smt2_bvuge(
        smt2_bvmul(
          smt2_function_applicationt{smt2_zero_extend(width),
                                     {convert_expr(expr.op0())}},
          smt2_function_applicationt{smt2_zero_extend(width),
                                     {convert_expr(expr.op1())}}),
        smt2_bv(power(2, width), width * 2));
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "overflow check should not be performed on unsupported type",
        op_type.id_string());
  }
  else if(expr.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    return smt2_symbolt((id2string(it->second)));
  }
  else if(expr.id()==ID_literal)
  {
    return convert_literal(to_literal_expr(expr).get_literal());
  }
  else if(expr.id()==ID_forall ||
          expr.id()==ID_exists)
  {
    const quantifier_exprt &quantifier_expr = to_quantifier_expr(expr);

    if(solver==solvert::MATHSAT)
      // NOLINTNEXTLINE(readability/throw)
      throw "MathSAT does not support quantifiers";

    exprt bound=expr.op0();
    smt2_astt bound_ast = convert_expr(bound);
    INVARIANT(
      bound_ast.id() == ID_symbol, "quantifier bound should be a symbol");
    const auto &bound_symbol = static_cast<const smt2_symbolt &>(bound_ast);
    smt2_sortt bound_type_ast = convert_type(bound.type());
    auto where_ast = convert_expr(quantifier_expr.where());

    if(quantifier_expr.id() == ID_forall)
    {
      return smt2_forallt(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>>{
          {smt2_pairt<smt2_symbolt, smt2_sortt>{bound_symbol,
                                                std::move(bound_type_ast)}}},
        std::move(where_ast));
    }
    return smt2_existst(
      smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>>{
        {smt2_pairt<smt2_symbolt, smt2_sortt>(
          bound_symbol, std::move(bound_type_ast))}},
      std::move(where_ast));
  }
  else if(expr.id()==ID_vector)
  {
    const vector_exprt &vector_expr = to_vector_expr(expr);
    const vector_typet &vector_type = to_vector_type(vector_expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    DATA_INVARIANT(
      size == vector_expr.operands().size(),
      "size indicated by type shall be equal to the number of operands");

    auto function_name = smt2_symbolt([&]() -> std::string {
      if(!use_datatypes)
        return "concat";
      const std::string &smt_typename = datatype_map.at(vector_type);
      return "mk-" + smt_typename;
    }());

    smt2_function_applicationt application{
      smt2_identifiert{std::move(function_name)}, {}};

    // build component-by-component
    forall_operands(it, vector_expr)
      application.add_argument(convert_expr(*it));
  }
  else if(expr.id()==ID_object_size)
  {
    return smt2_symbolt(id2string(object_sizes[expr]));
  }
  else if(expr.id()==ID_let)
  {
    const let_exprt &let_expr=to_let_expr(expr);
    auto symbol_ast = convert_expr(let_expr.symbol());
    CHECK_RETURN(symbol_ast.id() == ID_symbol);
    auto &smt2_symbol = static_cast<smt2_symbolt &>(symbol_ast);
    return smt2_lett(
      smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
        {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbol,
                                             convert_expr(let_expr.value())}}},
      convert_expr(let_expr.where()));
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    UNEXPECTEDCASE(
      "smt2_convt::convert_expr: `"+expr.id_string()+
      "' is not yet supported");
  }
  else if(expr.id() == ID_bswap)
  {
    const bswap_exprt &bswap_expr = to_bswap_expr(expr);

    DATA_INVARIANT(
      bswap_expr.op().type() == bswap_expr.type(),
      "operand of byte swap expression shall have same type as the expression");

    auto node = [&]() -> smt2_astt {
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
          "bit width indicated by type of bswap expression should be a "
          "multiple "
          "of the number of bits per byte");

        const std::size_t bytes = width / bits_per_byte;

        if(bytes <= 1)
          return smt2_symbolt{"bswap_op"};
        else
        {
          // do a parallel 'let' for each byte
          std::vector<smt2_pairt<smt2_symbolt, smt2_astt>> list;

          for(std::size_t byte = 0; byte < bytes; byte++)
          {
            list.emplace_back(
              smt2_symbolt("bswap_byte_" + std::to_string(byte)),
              smt2_function_applicationt{
                smt2_extract(
                  byte * bits_per_byte + (bits_per_byte - 1),
                  byte * bits_per_byte),
                {smt2_symbolt{"bswap_op"}}});
          }

          smt2_function_applicationt concat{
            smt2_identifiert{smt2_symbolt{"concat"}}, {}};
          for(std::size_t byte = 0; byte < bytes; byte++)
          {
            concat.add_argument(
              smt2_symbolt("bswap_byte_" + std::to_string(byte)));
          }

          return smt2_lett{
            smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{std::move(list)},
            std::move(concat)};
        }
      }
      else
        UNEXPECTEDCASE("bswap must get bitvector operand");
      UNREACHABLE;
    }();
    return smt2_lett(
      smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
        {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("bswap_op"),
                                             convert_expr(bswap_expr.op())}}},
      std::move(node));
  }
  else if(expr.id() == ID_popcount)
  {
    exprt lowered = lower_popcount(to_popcount_expr(expr), ns);
    return convert_expr(lowered);
  }
  else
    INVARIANT_WITH_DIAGNOSTICS(
      false,
      "smt2_convt::convert_expr should not be applied to unsupported type",
      expr.id_string());
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_typecast(const typecast_exprt &expr)
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
      return smt2_not(
        smt2_eq(convert_expr(src), convert_expr(from_integer(0, src_type))));
    }
    else if(src_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        return smt2_not(smt2_fp_is_zero(convert_expr(src)));
      }
      else
        return convert_floatbv(expr);
    }
    else
    {
      UNEXPECTEDCASE("TODO typecast1 "+src_type.id_string()+" -> bool");
    }
  }
  else if(dest_type.id()==ID_c_bool)
  {
    std::size_t to_width=boolbv_width(dest_type);
    return smt2_ite(
      smt2_not(
        smt2_eq(convert_expr(src), convert_expr(from_integer(0, src_type)))),
      smt2_bv(1, to_width),
      smt2_bv(0, to_width));
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
        return convert_expr(src);  // ignore
      else if(from_width<to_width) // extend
      {
        smt2_identifiert function_id =
          src_type.id() == ID_signedbv
            ? smt2_sign_extend(smt2_constantt::make(to_width - from_width))
            : smt2_zero_extend(to_width - from_width);
        return smt2_function_applicationt{std::move(function_id),
                                          {convert_expr(src)}};
      }
      else // chop off extra bits
      {
        return smt2_function_applicationt{smt2_extract(to_width - 1, 0),
                                          {convert_expr(src)}};
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
      return smt2_function_applicationt(
        smt2_identifiert{smt2_symbolt{"?tcop"}},
        {convert_expr(src),
         smt2_bvadd(
           [&] {
             if(to_width > from_integer_bits)
             {
               return smt2_function_applicationt{
                 smt2_sign_extend(
                   smt2_constantt::make(to_width - from_integer_bits)),
                 {smt2_function_applicationt{
                   smt2_extract(from_width - 1, from_fraction_bits),
                   {convert_expr(src)}}}};
             }
             else
             {
               return smt2_function_applicationt{
                 smt2_extract(
                   from_fraction_bits + to_width - 1, from_fraction_bits),
                 {convert_expr(src)}};
             }
           }(),
           smt2_ite(
             smt2_and(
               smt2_not(smt2_eq(
                 smt2_function_applicationt{
                   smt2_extract(from_fraction_bits - 1, 0),
                   {smt2_symbolt("?tcop")}},
                 smt2_bv(0, from_fraction_bits))),
               smt2_eq(
                 smt2_function_applicationt{
                   smt2_extract(from_width - 1, from_width - 1),
                   {smt2_symbolt("?tcop")}},
                 smt2_symbolt("#b1"))),
             smt2_bv(1, to_width),
             smt2_bv(0, to_width)))});
    }
    else if(src_type.id() == ID_floatbv) // from floatbv to int
    {
      if(dest_type.id()==ID_bv)
      {
        // this is _NOT_ a semantic conversion, but bit-wise

        if(use_FPA_theory)
        {
          // This conversion is non-trivial as it requires creating a
          // new bit-vector variable and then asserting that it converts
          // to the required floating-point number.
          SMT2_TODO("bit-wise floatbv to bv");
        }
        else
        {
          // straight-forward if width matches
          return convert_expr(src);
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
      auto cond = convert_expr(src);

      if(dest_type.id()==ID_fixedbv)
      {
        fixedbv_spect spec(to_fixedbv_type(dest_type));
        return smt2_ite(
          cond,
          smt2_concat(
            smt2_bv(1, spec.integer_bits),
            smt2_bv(0, spec.get_fraction_bits())),
          smt2_bv(0, spec.width));
      }
      else
      {
        return smt2_ite(cond, smt2_bv(1, to_width), smt2_bv(0, to_width));
      }
    }
    else if(src_type.id()==ID_pointer) // from pointer to int
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width<to_width) // extend
      {
        return smt2_function_applicationt{
          smt2_sign_extend(smt2_constantt::make(to_width - from_width)),
          {convert_expr(src)}};
      }
      else // chop off extra bits
      {
        return smt2_function_applicationt{smt2_extract(to_width - 1, 0),
                                          {convert_expr(src)}};
      }
    }
    else if(src_type.id()==ID_integer) // from integer to bit-vector
    {
      // must be constant
      if(src.is_constant())
      {
        return smt2_bv(
          numeric_cast_v<mp_integer>(to_constant_expr(src)), to_width);
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
        return flatten2bv(src);
      }
      else
      {
        INVARIANT(
          boolbv_width(src_type) == boolbv_width(dest_type),
          "bit vector with of source and destination type shall be equal");
        return convert_expr(src); // nothing else to do!
      }
    }
    else if(
      src_type.id() == ID_union ||
      src_type.id() == ID_union_tag) // flatten a union
    {
      INVARIANT(
        boolbv_width(src_type) == boolbv_width(dest_type),
        "bit vector with of source and destination type shall be equal");
      return convert_expr(src); // nothing else to do!
    }
    else if(src_type.id()==ID_c_bit_field)
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        return convert_expr(src); // ignore
      else
      {
        typet t=c_bit_field_replacement_type(to_c_bit_field_type(src_type), ns);
        typecast_exprt tmp(typecast_exprt(src, t), dest_type);
        return convert_typecast(tmp);
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
      return smt2_concat(
        [&]() -> smt2_astt {
          if(from_width == to_integer_bits)
            return convert_expr(src);
          else if(from_width > to_integer_bits)
          {
            // too many integer bits
            return smt2_function_applicationt(
              smt2_extract((to_integer_bits - 1), 0), {convert_expr(src)});
          }
          else
          {
            // too few integer bits
            INVARIANT(
              from_width < to_integer_bits,
              "from_width should be smaller than to_integer_bits as other case "
              "have been handled above");
            if(dest_type.id() == ID_unsignedbv)
            {
              return smt2_function_applicationt(
                smt2_zero_extend(to_integer_bits - from_width),
                {convert_expr(src)});
            }
            else
            {
              return smt2_function_applicationt(
                smt2_sign_extend(
                  smt2_constantt::make(to_integer_bits - from_width)),
                {convert_expr(src)});
            }
          }
        }(),
        smt2_bv(0, to_fraction_bits));
    }
    else if(src_type.id()==ID_bool) // bool to fixedbv
    {
      return smt2_concat(
        smt2_concat(smt2_bv(0, to_integer_bits - 1), flatten2bv(src)),
        smt2_bv(0, to_fraction_bits));
    }
    else if(src_type.id()==ID_fixedbv) // fixedbv to fixedbv
    {
      const fixedbv_typet &from_fixedbv_type=to_fixedbv_type(src_type);
      std::size_t from_fraction_bits=from_fixedbv_type.get_fraction_bits();
      std::size_t from_integer_bits=from_fixedbv_type.get_integer_bits();
      std::size_t from_width=from_fixedbv_type.get_width();

      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?tcop"),
                                               convert_expr(src)}}},
        smt2_concat(
          [&]() -> smt2_astt {
            if(to_integer_bits <= from_integer_bits)
            {
              return smt2_function_applicationt(
                smt2_extract(
                  from_fraction_bits + to_integer_bits - 1, from_fraction_bits),
                {smt2_symbolt("?tcop")});
            }
            else
            {
              INVARIANT(
                to_integer_bits > from_integer_bits,
                "to_integer_bits should be greater than from_integer_bits as "
                "the"
                "other case has been handled above");
              return smt2_function_applicationt(
                smt2_sign_extend(
                  smt2_constantt::make(to_integer_bits - from_integer_bits)),
                {smt2_function_applicationt{
                  smt2_extract(from_width - 1, from_fraction_bits),
                  {smt2_symbolt("?tcop")}}});
            }
          }(),
          smt2_concat(
            [&]() -> smt2_astt {
              if(to_fraction_bits <= from_fraction_bits)
              {
                return smt2_function_applicationt{
                  smt2_extract(
                    from_fraction_bits - 1,
                    from_fraction_bits - to_fraction_bits),
                  {smt2_symbolt("?tcop")}};
              }
              else
              {
                INVARIANT(
                  to_fraction_bits > from_fraction_bits,
                  "to_fraction_bits should be greater than from_fraction_bits "
                  "as "
                  "the other case has been handled above");
                return smt2_concat(
                  smt2_function_applicationt{
                    smt2_extract(from_fraction_bits - 1, 0),
                    {convert_expr(src)}},
                  smt2_bv(0, to_fraction_bits - from_fraction_bits));
              }
            }(),
            smt2_symbolt{"TODO: missing argument"})));
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
      return convert_expr(src);
    }
    else if(
      src_type.id() == ID_unsignedbv || src_type.id() == ID_signedbv ||
      src_type.id() == ID_bv)
    {
      // integer to pointer

      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        return convert_expr(src);
      else if(from_width<to_width)
      {
        return smt2_function_applicationt{
          smt2_sign_extend(smt2_constantt::make(to_width - from_width)),
          {convert_expr(src)}};
      }
      else // from_width>to_width
      {
        return smt2_function_applicationt{smt2_extract(to_width, 0),
                                          {convert_expr(src)}};
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

      return smt2_ite(
        convert_expr(src),
        [&]() {
          significand = 1;
          exponent = 0;
          a.build(significand, exponent);
          val.set_value(integer2bvrep(a.pack(), a.spec.width()));
          return convert_constant(val);
        }(),
        [&]() {
          significand = 0;
          exponent = 0;
          a.build(significand, exponent);
          val.set_value(integer2bvrep(a.pack(), a.spec.width()));
          return convert_constant(val);
        }());
    }
    else if(src_type.id()==ID_c_bool)
    {
      // turn into proper bool
      const typecast_exprt tmp(src, bool_typet());
      return convert_typecast(typecast_exprt(tmp, dest_type));
    }
    else if(src_type.id() == ID_bv)
    {
      if(to_bv_type(src_type).get_width() != dest_floatbv_type.get_width())
      {
        UNEXPECTEDCASE("Typecast bv -> float with wrong width");
      }

      if(use_FPA_theory)
      {
        return smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt{"to_fp"},
                           {smt2_constantt::make(dest_floatbv_type.get_e())}},
          {convert_expr(src)}};
      }
      else
        return convert_expr(src);
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> float");
  }
  else if(dest_type.id()==ID_integer)
  {
    if(src_type.id()==ID_bool)
    {
      return smt2_ite(
        convert_expr(src), smt2_constantt::make(1), smt2_constantt::make(0));
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> integer");
  }
  else if(dest_type.id()==ID_c_bit_field)
  {
    std::size_t from_width=boolbv_width(src_type);
    std::size_t to_width=boolbv_width(dest_type);

    if(from_width==to_width)
      return convert_expr(src); // ignore
    else
    {
      typet t=c_bit_field_replacement_type(to_c_bit_field_type(dest_type), ns);
      typecast_exprt tmp(typecast_exprt(src, t), dest_type);
      return convert_typecast(tmp);
    }
  }
  else
    UNEXPECTEDCASE(
      "TODO typecast8 "+src_type.id_string()+" -> "+dest_type.id_string());
  UNREACHABLE;
}

smt2_astt
smt2_convt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
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
        return smt2_function_applicationt(
          smt2_identifiert{smt2_symbolt{"to_fp"},
                           {smt2_constantt::make(dst.get_e()),
                            smt2_constantt::make(dst.get_f() + 1)}},
          {convert_rounding_mode_FPA(expr.op1()), convert_expr(src)});
      }
      else
        return convert_floatbv(expr);
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
        return convert_floatbv(expr);
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
        return convert_floatbv(expr);
    }
    else if(src_type.id()==ID_c_enum_tag)
    {
      // enum to float

      // We first convert to 'underlying type'
      floatbv_typecast_exprt tmp=expr;
      tmp.op()=
        typecast_exprt(
          src,
          ns.follow_tag(to_c_enum_tag_type(src_type)).subtype());
      return convert_floatbv_typecast(tmp);
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
      return convert_floatbv(expr);
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
      return convert_floatbv(expr);
  }
  else
  {
    UNEXPECTEDCASE(
      "TODO typecast12 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_struct(const struct_exprt &expr)
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
    auto node = smt2_function_applicationt(
      smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}}, {});

    for(std::size_t i = 0; i < components.size(); ++i)
      node.add_argument(convert_expr(expr.operands()[i]));

    return std::move(node);
  }
  else
  {
    if(components.size()==1)
      return convert_expr(expr.op0());
    else
    {
      auto node = convert_expr(expr.op0());

      // SMT-LIB 2 concat is binary only
      for(std::size_t i = 1; i < components.size(); ++i)
      {
        node = smt2_concat(
          [&]() {
            exprt op = expr.operands()[i];
            // may need to flatten array-theory arrays in there
            if(op.type().id() == ID_array)
              return flatten_array(op);
            return convert_expr(op);
          }(),
          std::move(node));
      }

      return node;
    }
  }
}

/// produce a flat bit-vector for a given array of fixed size
smt2_astt smt2_convt::flatten_array(const exprt &expr)
{
  const array_typet &array_type = to_array_type(expr.type());
  const auto &size_expr = array_type.size();
  PRECONDITION(size_expr.id() == ID_constant);

  mp_integer size = numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
  CHECK_RETURN_WITH_DIAGNOSTICS(size != 0, "can't convert zero-sized array");

  auto concatenation = smt2_select(
    smt2_symbolt("?far"),
    convert_expr(from_integer(0, array_type.size().type())));
  for(mp_integer i = 1; i < size; ++i)
  {
    concatenation = smt2_concat(
      smt2_select(
        smt2_symbolt("?far"),
        convert_expr(from_integer(i - 1, array_type.size().type()))),
      std::move(concatenation));
  }
  return smt2_lett(
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
      {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?far"),
                                           convert_expr(expr)}}},
    std::move(concatenation));
}

smt2_astt smt2_convt::convert_union(const union_exprt &expr)
{
  const union_typet &union_type = to_union_type(ns.follow(expr.type()));
  const exprt &op=expr.op();

  std::size_t total_width=boolbv_width(union_type);
  CHECK_RETURN_WITH_DIAGNOSTICS(
    total_width != 0, "failed to get union width for union");

  std::size_t member_width=boolbv_width(op.type());
  CHECK_RETURN_WITH_DIAGNOSTICS(
    member_width != 0, "failed to get union member width for union");

  if(total_width==member_width)
  {
    return flatten2bv(op);
  }
  else
  {
    // we will pad with zeros, but non-det would be better
    INVARIANT(
      total_width > member_width,
      "total_width should be greater than member_width as member_width can be"
      "at most as large as total_width and the other case has been handled "
      "above");
    return smt2_concat(smt2_bv(0, total_width - member_width), flatten2bv(op));
  }
}

smt2_astt smt2_convt::convert_constant(const constant_exprt &expr)
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
    return smt2_bv(value, width);
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    const fixedbv_spect spec(to_fixedbv_type(expr_type));

    const mp_integer v = bvrep2integer(expr.get_value(), spec.width, false);
    return smt2_bv(v, spec.width);
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
        return smt2_identifiert{
          smt2_symbolt{"NaN"},
          {smt2_constantt::make(e), smt2_constantt::make(f)}};
      }
      else if(v.is_infinity())
      {
        if(v.get_sign())
          return smt2_identifiert(
            smt2_symbolt("-oo"),
            {smt2_constantt::make(e), smt2_constantt::make(f)});
        else
          return smt2_identifiert(
            smt2_symbolt("+oo"),
            {smt2_constantt::make(e), smt2_constantt::make(f)});
      }
      else
      {
        // Zero, normal or subnormal

        mp_integer binary = v.pack();
        std::string binaryString(integer2binary(v.pack(), v.spec.width()));
        return smt2_identifiert(
          smt2_symbolt{"fp"},
          {smt2_binary_literalt(binaryString.substr(0, 1)),
           smt2_binary_literalt(binaryString.substr(1, e)),
           smt2_binary_literalt(binaryString.substr(1 + e, f - 1))});
      }
    }
    else
    {
      // produce corresponding bit-vector
      const ieee_float_spect spec(floatbv_type);
      const mp_integer v = bvrep2integer(expr.get_value(), spec.width(), false);
      return smt2_bv(v, spec.width());
    }
  }
  else if(expr_type.id()==ID_pointer)
  {
    const irep_idt &value = expr.get_value();

    if(value==ID_NULL)
    {
      return smt2_bv(0, boolbv_width(expr_type));
    }
    else
      UNEXPECTEDCASE("unknown pointer constant: "+id2string(value));
  }
  else if(expr_type.id()==ID_bool)
  {
    if(expr.is_true())
      return smt2_symbolt("true");
    else if(expr.is_false())
      return smt2_symbolt("false");
    else
      UNEXPECTEDCASE("unknown Boolean constant");
  }
  else if(expr_type.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    CHECK_RETURN(it != defined_expressions.end());
    return smt2_symbolt(id2string(it->second));
  }
  else if(expr_type.id()==ID_rational)
  {
    std::string value=id2string(expr.get_value());
    size_t pos=value.find("/");

    if(pos==std::string::npos)
      return smt2_symbolt(value + ".0");
    else
    {
      return smt2_function_applicationt(
        smt2_identifiert{smt2_symbolt{"/"}},
        {smt2_symbolt(value.substr(0, pos) + ".0"),
         smt2_symbolt(value.substr(pos + 1) + ".0")});
    }
  }
  else if(expr_type.id()==ID_integer)
  {
    return smt2_symbolt(id2string(expr.get_value()));
  }
  else
    UNEXPECTEDCASE("unknown constant: "+expr_type.id_string());
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_mod(const mod_exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
    {
      return smt2_bvurem(convert_expr(expr.op0()), convert_expr(expr.op1()));
    }
    return smt2_bvsrem(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else
    UNEXPECTEDCASE("unsupported type for mod: "+expr.type().id_string());
}

smt2_astt smt2_convt::convert_is_dynamic_object(const exprt &expr)
{
  std::vector<std::size_t> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  DATA_INVARIANT(
    expr.operands().size() == 1,
    "is_dynamic_object expression should have one operand");

  if(dynamic_objects.empty())
    return smt2_symbolt("false");

  std::size_t pointer_width = boolbv_width(expr.op0().type());

  return smt2_lett(
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
      {smt2_pairt<smt2_symbolt, smt2_astt>{
        smt2_symbolt("?obj"),
        smt2_function_applicationt{
          smt2_extract(
            pointer_width - 1, pointer_width - config.bv_encoding.object_bits),
          {convert_expr(expr.op0())}}}}},
    [&]() -> smt2_astt {
      if(dynamic_objects.size() == 1)
      {
        return smt2_eq(
          smt2_bv(dynamic_objects.front(), config.bv_encoding.object_bits),
          smt2_symbolt("?obj"));
      }
      auto node =
        smt2_function_applicationt(smt2_identifiert{smt2_symbolt{"or"}}, {});
      for(const auto &object : dynamic_objects)
      {
        node.add_argument(smt2_eq(
          smt2_bv(object, config.bv_encoding.object_bits),
          smt2_symbolt("?obj")));
      }
      return std::move(node);
    }());
}

smt2_astt smt2_convt::convert_relation(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 2);

  const typet &op_type=expr.op0().type();

  if(op_type.id()==ID_unsignedbv ||
     op_type.id()==ID_pointer ||
     op_type.id()==ID_bv)
  {
    auto function_name = [&]() {
      if(expr.id() == ID_le)
        return smt2_symbolt{"bvule"};
      else if(expr.id() == ID_lt)
        return smt2_symbolt{"bvult"};
      else if(expr.id() == ID_ge)
        return smt2_symbolt{"bvuge"};
      else if(expr.id() == ID_gt)
        return smt2_symbolt{"bvugt"};
      UNREACHABLE;
    }();

    return smt2_function_applicationt(
      smt2_identifiert{std::move(function_name)},
      {convert_expr(expr.op0()), convert_expr(expr.op1())});
  }
  else if(op_type.id()==ID_signedbv ||
          op_type.id()==ID_fixedbv)
  {
    auto function_name = [&]() {
      if(expr.id() == ID_le)
        return smt2_symbolt("bvsle");
      else if(expr.id() == ID_lt)
        return smt2_symbolt("bvslt");
      else if(expr.id() == ID_ge)
        return smt2_symbolt("bvsge");
      else if(expr.id() == ID_gt)
        return smt2_symbolt("bvsgt");
      UNREACHABLE;
    }();

    return smt2_function_applicationt(
      smt2_identifiert{std::move(function_name)},
      {convert_expr(expr.op0()), convert_expr(expr.op1())});
  }
  else if(op_type.id()==ID_floatbv)
  {
    if(use_FPA_theory)
    {
      auto function_name = [&]() {
        if(expr.id() == ID_le)
          return smt2_symbolt("fp.leq");
        else if(expr.id() == ID_lt)
          return smt2_symbolt("fp.lt");
        else if(expr.id() == ID_ge)
          return smt2_symbolt("fp.geq");
        else if(expr.id() == ID_gt)
          return smt2_symbolt("fp.gt");
        UNREACHABLE;
      }();

      return smt2_function_applicationt(
        smt2_identifiert{std::move(function_name)},
        {convert_expr(expr.op0()), convert_expr(expr.op1())});
    }
    else
      return convert_floatbv(expr);
  }
  else if(op_type.id()==ID_rational ||
          op_type.id()==ID_integer)
  {
    return smt2_function_applicationt(
      smt2_identifiert{smt2_symbolt{expr.id()}},
      {convert_expr(expr.op0()), convert_expr(expr.op1())});
  }
  else
    UNEXPECTEDCASE(
      "unsupported type for "+expr.id_string()+": "+op_type.id_string());
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_plus(const plus_exprt &expr)
{
  if(
    expr.type().id() == ID_rational || expr.type().id() == ID_integer ||
    expr.type().id() == ID_real)
  {
    // these are multi-ary in SMT-LIB2
    smt2_function_applicationt function{smt2_identifiert{smt2_symbolt{ID_plus}},
                                        {}};
    for(const auto &op : expr.operands())
      function.add_argument(convert_expr(op));
    return std::move(function);
  }
  else if(
    expr.type().id() == ID_unsignedbv || expr.type().id() == ID_signedbv ||
    expr.type().id() == ID_fixedbv)
  {
    // These could be chained, i.e., need not be binary,
    // but at least MathSat doesn't like that.
    if(expr.operands().size() == 2)
    {
      return smt2_bvadd(convert_expr(expr.op0()), convert_expr(expr.op1()));
    }
    return convert_plus(to_plus_expr(make_binary(expr)));
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
    if(expr.operands().size() != 2)
      return convert_plus(to_plus_expr(make_binary(expr)));

    exprt p = expr.op0(), i = expr.op1();

    if(p.type().id() != ID_pointer)
      p.swap(i);

    DATA_INVARIANT(
      p.type().id() == ID_pointer,
      "one of the operands should have pointer type");

    const auto element_size = pointer_offset_size(expr.type().subtype(), ns);
    CHECK_RETURN(element_size.has_value() && *element_size >= 1);

    auto second_element = [&]() {
      if(*element_size < 2)
        return convert_expr(i);
      return smt2_bvmul(
        convert_expr(i), smt2_bv(*element_size, boolbv_width(expr.type())));
    }();

    return smt2_bvadd(convert_expr(p), std::move(second_element));
  }
  else if(expr.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(expr.type());
    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());
    typet index_type = vector_type.size().type();

    auto function_name = [&]() {
      if(!use_datatypes)
        return smt2_symbolt("concat");
      const std::string &smt_typename = datatype_map.at(vector_type);
      return smt2_symbolt("mk-" + smt_typename);
    }();
    smt2_function_applicationt function{
      smt2_identifiert{std::move(function_name)}, {}};

    // add component-by-component
    for(mp_integer i = 0; i != size; ++i)
    {
      exprt::operandst summands;
      summands.reserve(expr.operands().size());
      for(const auto &op : expr.operands())
        summands.push_back(index_exprt(
          op, from_integer(size - i - 1, index_type), vector_type.subtype()));

      function.add_argument(
        convert_expr(plus_exprt(std::move(summands), vector_type.subtype())));
    }

    return std::move(function);
  }
  else
    UNEXPECTEDCASE("unsupported type for +: " + expr.type().id_string());
}

/// Converting a constant or symbolic rounding mode to SMT-LIB. Only called when
/// use_FPA_theory is enabled
/// \par parameters: The expression representing the rounding mode.
/// \return SMT-LIB output to out.
smt2_astt smt2_convt::convert_rounding_mode_FPA(const exprt &expr)
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

  if(expr.id()==ID_constant)
  {
    const constant_exprt &cexpr=to_constant_expr(expr);

    mp_integer value = numeric_cast_v<mp_integer>(cexpr);

    if(value==0)
      return smt2_symbolt{"roundNearestTiesToEven"};
    else if(value==1)
      return smt2_symbolt{"roundTowardNegative"};
    else if(value==2)
      return smt2_symbolt{"roundTowardPositive"};
    else if(value==3)
      return smt2_symbolt{"roundTowardZero"};
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "Rounding mode should have value 0, 1, 2, or 3",
        id2string(cexpr.get_value()));
  }
  else
  {
    std::size_t width=to_bitvector_type(expr.type()).get_width();

    auto converted = convert_expr(expr);
    // Need to make the choice above part of the model
    return smt2_ite(
      smt2_eq(smt2_bv(0, width), converted),
      smt2_symbolt{"roundNearestTiesToEven"},
      smt2_ite(
        smt2_eq(smt2_bv(1, width), converted),
        smt2_symbolt{"roundTowardNegative"},
        smt2_ite(
          smt2_eq(smt2_bv(2, width), converted),
          smt2_symbolt{"roundTowardPositve"},
          // TODO: add some kind of error checking here
          smt2_symbolt{"roundTowardZero"})));
  }
}

smt2_astt smt2_convt::convert_floatbv_plus(const ieee_float_op_exprt &expr)
{
  const typet &type=expr.type();

  PRECONDITION(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex && type.subtype().id() == ID_floatbv) ||
    (type.id() == ID_vector && type.subtype().id() == ID_floatbv));

  if(use_FPA_theory)
  {
    if(type.id()==ID_floatbv)
    {
      return smt2_fp_add(
        convert_rounding_mode_FPA(expr.rounding_mode()),
        convert_expr(expr.lhs()),
        convert_expr(expr.rhs()));
    }
    else if(type.id()==ID_complex)
    {
      SMT2_TODO("+ for floatbv complex");
    }
    else if(type.id()==ID_vector)
    {
      SMT2_TODO("+ for floatbv vector");
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "type should not be one of the unsupported types",
        type.id_string());
  }
  else
    return convert_floatbv(expr);
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_minus(const minus_exprt &expr)
{
  if(expr.type().id()==ID_integer)
  {
    return smt2_minus(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    if(expr.op0().type().id()==ID_pointer &&
       expr.op1().type().id()==ID_pointer)
    {
      // Pointer difference
      auto element_size = pointer_offset_size(expr.op0().type().subtype(), ns);
      CHECK_RETURN(element_size.has_value() && *element_size >= 1);


      INVARIANT(
        boolbv_width(expr.op0().type()) == boolbv_width(expr.type()),
        "bitvector width of operand shall be equal to the bitvector width of "
        "the expression");

      auto sub = smt2_bvsub(convert_expr(expr.op0()), convert_expr(expr.op1()));

      if(*element_size >= 2)
      {
        return smt2_bvsdiv(
          std::move(sub), smt2_bv(*element_size, boolbv_width(expr.type())));
      }
      return sub;
    }
    else
    {
      return smt2_bvsub(convert_expr(expr.op0()), convert_expr(expr.op1()));
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
    SMT2_TODO("pointer subtraction");
  }
  else if(expr.type().id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    typet index_type=vector_type.size().type();

    auto function_name = [&]() {
      if(use_datatypes)
      {
        const std::string &smt_typename = datatype_map.at(vector_type);
        return smt2_symbolt{"mk-" + smt_typename};
      }
      return smt2_symbolt{"concat"};
    }();
    smt2_function_applicationt node{smt2_identifiert{std::move(function_name)},
                                    {}};

    // subtract component-by-component
    for(mp_integer i=0; i!=size; ++i)
    {
      exprt tmp(ID_minus, vector_type.subtype());
      forall_operands(it, expr)
        tmp.copy_to_operands(
          index_exprt(
            *it,
            from_integer(size-i-1, index_type),
            vector_type.subtype()));
      node.add_argument(convert_expr(tmp));
    }
    return std::move(node);
  }
  else
    UNEXPECTEDCASE("unsupported type for -: "+expr.type().id_string());
}

smt2_astt smt2_convt::convert_floatbv_minus(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    return smt2_fp_sub(
      convert_rounding_mode_FPA(expr.rounding_mode()),
      convert_expr(expr.lhs()),
      convert_expr(expr.rhs()));
  }
  else
    return convert_floatbv(expr);
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_div(const div_exprt &expr)
{
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
    {
      return smt2_bvudiv(convert_expr(expr.op0()), convert_expr(expr.op1()));
    }
    return smt2_bvsdiv(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));
    std::size_t fraction_bits=spec.get_fraction_bits();

    return smt2_function_applicationt{
      smt2_extract(spec.width - 1, 0),
      {smt2_bvsdiv(
        smt2_concat(convert_expr(expr.op0()), smt2_bv(0, fraction_bits)),
        smt2_function_applicationt{
          smt2_sign_extend(smt2_constantt::make(fraction_bits)),
          {convert_expr(expr.op1())}})}};
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

smt2_astt smt2_convt::convert_floatbv_div(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    return smt2_fp_div(
      convert_rounding_mode_FPA(expr.rounding_mode()),
      convert_expr(expr.lhs()),
      convert_expr(expr.rhs()));
  }
  else
    return convert_floatbv(expr);
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_mult(const mult_exprt &expr)
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
    return smt2_bvmul(convert_expr(expr.op0()), convert_expr(expr.op1()));
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
    return smt2_function_applicationt{
      smt2_extract(spec.width + fraction_bits - 1, fraction_bits),
      {smt2_bvmul(
        smt2_function_applicationt{
          smt2_sign_extend(smt2_constantt::make(fraction_bits)),
          {convert_expr(expr.op0())}},
        smt2_function_applicationt{
          smt2_sign_extend(smt2_constantt::make(fraction_bits)),
          {convert_expr(expr.op1())}})}};
  }
  else if(expr.type().id()==ID_rational ||
          expr.type().id()==ID_integer ||
          expr.type().id()==ID_real)
  {
    smt2_function_applicationt node(smt2_identifiert{smt2_symbolt{"*"}}, {});

    for(const exprt &op : expr.operands())
      node.add_argument(convert_expr(op));
    return std::move(node);
  }
  else
    UNEXPECTEDCASE("unsupported type for *: "+expr.type().id_string());
}

smt2_astt smt2_convt::convert_floatbv_mult(const ieee_float_op_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  if(use_FPA_theory)
  {
    return smt2_fp_mul(
      convert_rounding_mode_FPA(expr.rounding_mode()),
      convert_expr(expr.lhs()),
      convert_expr(expr.rhs()));
  }
  else
    return convert_floatbv(expr);
  UNREACHABLE;
}

smt2_astt smt2_convt::convert_with(const with_exprt &expr)
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
      return smt2_function_applicationt(
        smt2_identifiert{smt2_symbolt{"store"}},
        {convert_expr(expr.old()),
         convert_expr(typecast_exprt(expr.where(), array_type.size().type())),
         convert_expr(expr.new_value())});
    }
    else
    {
      // fixed-width
      std::size_t array_width=boolbv_width(array_type);
      std::size_t sub_width=boolbv_width(array_type.subtype());
      std::size_t index_width=boolbv_width(expr.where().type());

      // We mask out the updated bits with AND,
      // and then OR-in the shifted new value.
      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{
            smt2_symbolt("distance?"),
            smt2_bvmul(
              smt2_bv(sub_width, array_width),
              [&]() {
                // SMT2 says that the shift distance needs to be as wide
                // as the stuff we are shifting.
                if(array_width > index_width)
                {
                  return smt2_function_applicationt{
                    smt2_zero_extend(array_width - index_width),
                    {convert_expr(expr.where())}};
                }
                return smt2_function_applicationt{
                  smt2_extract(array_width - 1, 0),
                  {convert_expr(expr.where())}};
              }())}}},
        smt2_bvor(
          smt2_bvand(
            smt2_bvnot(smt2_bvshl(
              smt2_bv(power(2, sub_width) - 1, array_width),
              smt2_symbolt("distance?"))),
            convert_expr(expr.old())),
          smt2_bvshl(
            smt2_function_applicationt{
              smt2_zero_extend(array_width - sub_width),
              {convert_expr(expr.new_value())}},
            smt2_symbolt("distance?"))));
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
      return smt2_function_applicationt(
        smt2_identifiert{smt2_symbolt{"update-" + smt_typename + "." +
                                      id2string(component_name)}},
        {convert_expr(expr.old()), convert_expr(value)});
    }
    else
    {
      std::size_t struct_width=boolbv_width(struct_type);

      // figure out the offset and width of the member
      boolbv_widtht::membert m=
        boolbv_width.get_member(struct_type, component_name);

      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?withop"),
                                               convert_expr(expr.old())}}},
        [&]() {
          if(m.width == struct_width)
          {
            // the struct is the same as the member, no concat needed,
            // ?withop won't be used
            return convert_expr(value);
          }
          else if(m.offset == 0)
          {
            // the member is at the beginning
            return smt2_concat(
              smt2_function_applicationt{
                smt2_extract(struct_width - 1, m.width),
                {smt2_symbolt("?withop")}},
              convert_expr(value));
          }
          else if(m.offset + m.width == struct_width)
          {
            // the member is at the end
            return smt2_concat(
              convert_expr(value),
              smt2_function_applicationt{smt2_extract(m.offset - 1, 0),
                                         {smt2_symbolt("?withop")}});
          }
          else
          {
            // most general case, need two concat-s
            return smt2_concat(
              smt2_concat(
                smt2_function_applicationt{
                  smt2_extract(struct_width - 1, m.offset + m.width),
                  {smt2_symbolt("?withop")}},
                convert_expr(value)),
              smt2_function_applicationt{smt2_extract(m.offset - 1, 0),
                                         {smt2_symbolt("?withop")}});
          }
        }());
    }
  }
  else if(expr_type.id() == ID_union || expr_type.id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(expr_type));

    const exprt &value = expr.new_value();

    std::size_t total_width=boolbv_width(union_type);
    CHECK_RETURN_WITH_DIAGNOSTICS(
      total_width != 0, "failed to get union width for with");

    std::size_t member_width=boolbv_width(value.type());
    CHECK_RETURN_WITH_DIAGNOSTICS(
      member_width != 0, "failed to get union member width for with");

    if(total_width==member_width)
    {
      return flatten2bv(value);
    }
    else
    {
      INVARIANT(
        total_width > member_width,
        "total width should be greater than member_width as member_width is at "
        "most as large as total_width and the other case has been handled "
        "above");
      return smt2_concat(
        smt2_function_applicationt{smt2_extract(total_width - 1, member_width),
                                   {convert_expr(expr.old())}},
        flatten2bv(value));
    }
  }
  else if(expr_type.id()==ID_bv ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv)
  {
    // Update bits in a bit-vector. We will use masking and shifts.

    std::size_t total_width=boolbv_width(expr_type);
    CHECK_RETURN_WITH_DIAGNOSTICS(
      total_width != 0, "failed to get total width");

    const exprt &index=expr.operands()[1];
    const exprt &value=expr.operands()[2];

    std::size_t value_width=boolbv_width(value.type());
    CHECK_RETURN_WITH_DIAGNOSTICS(
      value_width != 0, "failed to get value width");

    typecast_exprt index_tc(index, expr_type);

    // TODO: SMT2-ify
    SMT2_TODO("SMT2-ify");

#if 0
    out << "(bvor ";
    out << "(band ";

    // the mask to get rid of the old bits
    out << " (bvnot (bvshl";

    out << " (concat";
    out << " (repeat[" << total_width-value_width << "] bv0[1])";
    out << " (repeat[" << value_width << "] bv1[1])";
    out << ")"; // concat

    // shift it to the index
    convert_expr(index_tc);
    out << "))"; // bvshl, bvot

    out << ")"; // bvand

    // the new value
    out << " (bvshl ";
    convert_expr(value);

    // shift it to the index
    convert_expr(index_tc);
    out << ")"; // bvshl

    out << ")"; // bvor
#endif
  }
  else
    UNEXPECTEDCASE(
      "with expects struct, union, or array type, but got "+
      expr.type().id_string());
}

smt2_astt smt2_convt::convert_update(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  SMT2_TODO("smt2_convt::convert_update to be implemented");
}

smt2_astt smt2_convt::convert_index(const index_exprt &expr)
{
  const typet &array_op_type = expr.array().type();

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(array_op_type);

    if(use_array_theory(expr.array()))
    {
      if(expr.type().id() == ID_bool && !use_array_of_bool)
      {
        return smt2_function_applicationt(
          smt2_identifiert{smt2_symbolt{"="}},
          {smt2_select(
             convert_expr(expr.array()),
             convert_expr(
               typecast_exprt(expr.index(), array_type.size().type()))),
           smt2_binary_literalt::make(1),
           smt2_binary_literalt::make(0)});
      }
      else
      {
        return smt2_select(
          convert_expr(expr.array()),
          convert_expr(typecast_exprt(expr.index(), array_type.size().type())));
      }
    }
    else
    {
      // fixed size
      std::size_t array_width=boolbv_width(array_type);
      CHECK_RETURN(array_width != 0);


      std::size_t sub_width=boolbv_width(array_type.subtype());
      std::size_t index_width=boolbv_width(expr.index().type());

      auto node = smt2_function_applicationt(
        smt2_extract(sub_width - 1, 0),
        {smt2_bvlshr(
          convert_expr(expr.array()),
          smt2_bvmul(smt2_bv(sub_width, array_width), [&] {
            // SMT2 says that the shift distance must be the same as
            // the width of what we shift.
            if(array_width > index_width)
            {
              return smt2_function_applicationt{
                smt2_zero_extend(array_width - index_width),
                {convert_expr(expr.index())}};
            }
            else
            {
              return smt2_function_applicationt{
                smt2_extract(array_width - 1, 0), {convert_expr(expr.index())}};
            }
          }()))});

      return unflatten(array_type.subtype(), std::move(node));
    }
  }
  else if(array_op_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(array_op_type);

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(vector_type);

      // this is easy for constant indicies

      const auto index_int = numeric_cast<mp_integer>(expr.index());
      if(!index_int.has_value())
      {
        SMT2_TODO("non-constant index on vectors");
      }
      else
      {
        return smt2_function_applicationt{
          smt2_identifiert{smt2_symbolt(
            smt_typename + "." + std::to_string(index_int->to_long()))},
          {convert_expr(expr.array())}};
      }
    }
    else
    {
      SMT2_TODO("index on vectors");
    }
  }
  else
    INVARIANT(
      false, "index with unsupported array type: " + array_op_type.id_string());
}

smt2_astt smt2_convt::convert_member(const member_exprt &expr)
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
      const std::string &component =
        id2string(struct_type.get_component(name).get_name());
      smt2_symbolt member_ast{std::string(smt_typename) + "." + component};
      return smt2_function_applicationt(
        smt2_identifiert{std::move(member_ast)}, {convert_expr(struct_op)});
    }
    else
    {
      // we extract
      const std::size_t member_width = boolbv_width(expr.type());
      const auto member_offset = member_offset_bits(struct_type, name, ns);

      CHECK_RETURN_WITH_DIAGNOSTICS(
        member_offset.has_value(), "failed to get struct member offset");

      return smt2_function_applicationt{
        smt2_extract(
          member_offset.value() + member_width - 1, member_offset.value()),
        {convert_expr(struct_op)}};
    }
  }
  else if(
    struct_op_type.id() == ID_union || struct_op_type.id() == ID_union_tag)
  {
    std::size_t width=boolbv_width(expr.type());
    CHECK_RETURN_WITH_DIAGNOSTICS(
      width != 0, "failed to get union member width");

    return unflatten(
      expr.type(),
      smt2_function_applicationt{smt2_extract(width - 1, 0),
                                 {convert_expr(struct_op)}});
  }
  else
    UNEXPECTEDCASE(
      "convert_member on an unexpected type "+struct_op_type.id_string());
}

smt2_astt smt2_convt::flatten2bv(const exprt &expr)
{
  const typet &type = expr.type();

  if(type.id()==ID_bool)
  {
    // expr returns a boolean and #b0 and #b1 are one-bit bit-vector
    return smt2_ite(
      convert_expr(expr), smt2_symbolt("#b1"), smt2_symbolt("#b0"));
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // concatenate elements
      const vector_typet &vector_type=to_vector_type(type);

      mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());
      smt2_function_applicationt concat(
        smt2_identifiert{smt2_symbolt{"concat"}}, {});
      for(mp_integer i=0; i!=size; ++i)
      {
        concat.add_argument(
          smt2_function_applicationt{smt2_identifiert{smt2_symbolt(
                                       smt_typename + "." + integer2string(i))},
                                     {smt2_symbolt("?vflop")}});
      }
      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?vflop"),
                                               convert_expr(expr)}}},
        std::move(concat));
    }
    else
      return convert_expr(expr); // already a bv
  }
  else if(type.id()==ID_array)
  {
    return convert_expr(expr);
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // concatenate elements
      const struct_typet &struct_type = to_struct_type(ns.follow(type));
      const struct_typet::componentst &components=
        struct_type.components();

      smt2_symbolt function_name{smt_typename + "." +
                                 id2string(components[0].get_name())};
      smt2_astt concat_node = smt2_function_applicationt(
        smt2_identifiert{std::move(function_name)}, {smt2_symbolt("?sflop")});

      // SMT-LIB 2 concat is binary only
      for(std::size_t i = 0; i < components.size(); ++i)
      {
        concat_node = smt2_concat(
          smt2_function_applicationt(
            smt2_identifiert{smt2_symbolt(
              smt_typename + "." + id2string(components[i - 1].get_name()))},
            {smt2_symbolt("?sflop")}),
          std::move(concat_node));
      }

      return smt2_lett(
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
          {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?sflop"),
                                               convert_expr(expr)}}},
        std::move(concat_node));
    }
    else
      return convert_expr(expr);
  }
  else if(type.id()==ID_floatbv)
  {
    INVARIANT(
      !use_FPA_theory,
      "floatbv expressions should be flattened when using FPA theory");

    return convert_expr(expr);
  }
  else
    return convert_expr(expr);
}

smt2_astt
smt2_convt::unflatten(const typet &type, smt2_astt ast, unsigned nesting)
{
  if(type.id()==ID_bool)
    return smt2_eq(std::move(ast), smt2_symbolt("#b1"));

  if(type.id() == ID_vector)
  {
    if(!use_datatypes)
    {
      // nothing to do, already a bv
      return ast;
    }

    return smt2_lett(
      smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
        {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?ufop"),
                                             smt2_constantt::make(nesting)}}},
      [&]() {
        const std::string &smt_typename = datatype_map.at(type);

        // extract elements
        const vector_typet &vector_type = to_vector_type(type);
        std::size_t subtype_width = boolbv_width(vector_type.subtype());
        mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());
        smt2_function_applicationt mk_fun(
          smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}}, {});
        std::size_t offset=0;

        for(mp_integer i=0; i!=size; ++i, offset+=subtype_width)
        {
          auto extract = smt2_function_applicationt(
            smt2_extract(offset + subtype_width - 1, offset),
            {smt2_symbolt("?ufop"), smt2_constantt::make(nesting)});
          mk_fun.add_argument(
            unflatten(vector_type.subtype(), std::move(extract), nesting + 1));
        }
        return mk_fun;
      }());
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(!use_datatypes)
    {
      // nothing to do, already a bv
      return ast;
    }

    return smt2_lett(
      smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>>{
        {smt2_pairt<smt2_symbolt, smt2_astt>{smt2_symbolt("?ufop"),
                                             smt2_constantt::make(nesting)}}},
      [&]() {
        // TODO ast is missing from here!!!
        // extract members
        const std::string &smt_typename = datatype_map.at(type);

        smt2_function_applicationt mk_fun{
          smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}}, {}};
        const struct_typet &struct_type = to_struct_type(ns.follow(type));
        const struct_typet::componentst &components=
          struct_type.components();

        std::size_t offset=0;
        std::size_t i = 0;
        for(struct_typet::componentst::const_iterator it = components.begin();
            it != components.end();
            it++, i++)
        {
          std::size_t member_width=boolbv_width(it->type());
          smt2_function_applicationt extract_node{
            smt2_extract(offset + member_width - 1, offset),
            {smt2_symbolt("?ufop"), smt2_constantt::make(nesting)}};
          mk_fun.add_argument(
            unflatten(it->type(), std::move(extract_node), nesting + 1));
          offset += member_width;
        }
        return mk_fun;
      }());
  }
  return ast;
}

void smt2_convt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id() == ID_bool);

  if(expr.id()==ID_and && value)
  {
    forall_operands(it, expr)
      set_to(*it, true);
    return;
  }

  if(expr.id()==ID_or && !value)
  {
    forall_operands(it, expr)
      set_to(*it, false);
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

    if(equal_expr.lhs().id()==ID_symbol)
    {
      const irep_idt &identifier=
        to_symbol_expr(equal_expr.lhs()).get_identifier();

      if(identifier_map.find(identifier)==identifier_map.end())
      {
        identifiert &id=identifier_map[identifier];
        CHECK_RETURN(id.type.is_nil());

        id.type=equal_expr.lhs().type();
        for(const auto &command : find_symbols(id.type))
          out << *command;
        const auto prepared_rhs_with_dependencies =
          prepare_for_convert_expr(equal_expr.rhs());
        const exprt &prepared_rhs = prepared_rhs_with_dependencies.second;

        std::string smt2_identifier=convert_identifier(identifier);
        smt2_identifiers.insert(smt2_identifier);

        for(const auto &command : prepared_rhs_with_dependencies.first)
          out << *command;

        out << smt2_commentt{"set_to true (equal)"};
        out << smt2_commandt::define_fun(
          smt2_symbolt{"|" + smt2_identifier + "|"},
          smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>>{{}},
          convert_type(equal_expr.lhs().type()),
          convert_expr(prepared_rhs));
        return; // done
      }
    }
  }

  const auto prepared_expr_with_dependencies = prepare_for_convert_expr(expr);
  const exprt &prepared_expr = prepared_expr_with_dependencies.second;

#if 0
  out << "; CONV: "
      << format(expr) << "\n";
#endif

  for(const auto &command : prepared_expr_with_dependencies.first)
    out << *command;

  smt2_astt assertion =
    value ? convert_expr(prepared_expr) : smt2_not(convert_expr(prepared_expr));
  out << "; set_to " << (value ? "true" : "false") << "\n"
      << smt2_commandt::_assert(std::move(assertion));
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
std::pair<std::list<std::unique_ptr<smt2_command_or_commentt>>, exprt>
smt2_convt::prepare_for_convert_expr(const exprt &expr)
{
  // First, replace byte operators, because they may introduce new array
  // expressions that must be seen by find_symbols:
  exprt lowered_expr = lower_byte_operators(expr);
  INVARIANT(
    !has_byte_operator(lowered_expr),
    "lower_byte_operators should remove all byte operators");

  // Now create symbols for all composite expressions present in lowered_expr:
  return std::make_pair(find_symbols(lowered_expr), lowered_expr);
}

std::list<std::unique_ptr<smt2_command_or_commentt>>
smt2_convt::find_symbols(const exprt &expr)
{
  // recursive call on type
  auto result = find_symbols(expr.type());

  if(expr.id() == ID_exists || expr.id() == ID_forall)
  {
    // do not declare the quantified symbol, but record
    // as 'bound symbol'
    const auto &q_expr = to_quantifier_expr(expr);
    const auto identifier = q_expr.symbol().get_identifier();
    identifiert &id = identifier_map[identifier];
    id.type = q_expr.symbol().type();
    id.is_bound = true;

    auto where_result = find_symbols(q_expr.where());
    result.splice(result.end(), where_result);
    return result;
  }

  // recursive call on operands
  forall_operands(it, expr)
    result.splice(result.end(), find_symbols(*it));

  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    // we don't track function-typed symbols
    if(expr.type().id()==ID_code)
      return result;

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

      result.push_back(util_make_unique<smt2_commentt>("find_symbols"));
      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_fun(
          smt2_symbolt{"|" + smt2_identifier + "|"},
          smt2_listt<smt2_sortt>{{}},
          convert_type(expr.type()))));
    }
  }
  else if(expr.id()==ID_array_of)
  {
    if(defined_expressions.find(expr)==defined_expressions.end())
    {
      const irep_idt id =
        "array_of." + std::to_string(defined_expressions.size());
      result.push_back(util_make_unique<smt2_commentt>(
        "the following is a substitute for lambda i. x"));
      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_fun(
          smt2_symbolt{id},
          smt2_listt<smt2_sortt>{{}},
          convert_type(expr.type()))));

      // use a quantifier instead of the lambda
      #if 0 // not really working in any solver yet!
      out << "(assert (forall ((i ";
      convert_type(array_index_type());
      out << ")) (= (select " << id << " i) ";
      convert_expr(expr.op0());
      out << ")))" << "\n";
      #endif

      defined_expressions[expr]=id;
    }
  }
  else if(expr.id()==ID_array)
  {
    if(defined_expressions.find(expr)==defined_expressions.end())
    {
      const array_typet &array_type=to_array_type(expr.type());

      const irep_idt id = "array." + std::to_string(defined_expressions.size());
      result.push_back(util_make_unique<smt2_commentt>(
        "the following is a substitute for an array constructor"));
      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_fun(
          smt2_symbolt{id},
          smt2_listt<smt2_sortt>{{}},
          convert_type(array_type))));

      for(std::size_t i=0; i<expr.operands().size(); i++)
      {
        result.push_back(
          util_make_unique<smt2_commandt>(smt2_commandt::_assert(smt2_eq(
            smt2_select(
              smt2_symbolt{id},
              convert_expr(from_integer(i, array_type.size().type()))),
            convert_expr(expr.operands()[i])))));
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
      result.push_back(util_make_unique<smt2_commentt>(
        "the following is a substitute for a string"));

      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_fun(
          smt2_symbolt{id},
          smt2_listt<smt2_sortt>{{}},
          convert_type(array_type))));

      for(std::size_t i=0; i<tmp.operands().size(); i++)
      {
        result.push_back(
          util_make_unique<smt2_commandt>(smt2_commandt::_assert(smt2_eq(
            smt2_select(
              smt2_symbolt{id},
              convert_expr(from_integer(i, array_type.size().type()))),
            convert_expr(tmp.operands()[i])))));
      }

      defined_expressions[expr]=id;
    }
  }
  else if(expr.id()==ID_object_size &&
          expr.operands().size()==1)
  {
    const exprt &op = expr.op0();

    if(op.type().id()==ID_pointer)
    {
      if(object_sizes.find(expr)==object_sizes.end())
      {
        const irep_idt id =
          "object_size." + std::to_string(object_sizes.size());
        result.push_back(
          util_make_unique<smt2_commandt>(smt2_commandt::declare_fun(
            smt2_symbolt{id},
            smt2_listt<smt2_sortt>{{}},
            convert_type(expr.type()))));

        object_sizes[expr]=id;
      }
    }
  }
  else if(!use_FPA_theory &&
          expr.operands().size()>=1 &&
          (expr.id()==ID_floatbv_plus ||
           expr.id()==ID_floatbv_minus ||
           expr.id()==ID_floatbv_mult ||
           expr.id()==ID_floatbv_div ||
           expr.id()==ID_floatbv_typecast ||
           expr.id()==ID_ieee_float_equal ||
           expr.id()==ID_ieee_float_notequal ||
           ((expr.id()==ID_lt ||
             expr.id()==ID_gt ||
             expr.id()==ID_le ||
             expr.id()==ID_ge ||
             expr.id()==ID_isnan ||
             expr.id()==ID_isnormal ||
             expr.id()==ID_isfinite ||
             expr.id()==ID_isinf ||
             expr.id()==ID_sign ||
             expr.id()==ID_unary_minus ||
             expr.id()==ID_typecast ||
             expr.id()==ID_abs) &&
             expr.op0().type().id()==ID_floatbv)))
  {
    irep_idt function=
      "|float_bv."+expr.id_string()+floatbv_suffix(expr)+"|";

    if(bvfp_set.insert(function).second)
    {
      result.push_back(util_make_unique<smt2_commentt>(
        "this is a model for " + id2string(expr.id()) + " : " +
        id2string(type2id(expr.op0().type())) + " -> " +
        id2string(type2id(expr.type()))));

      std::vector<smt2_pairt<smt2_symbolt, smt2_sortt>> args;
      for(std::size_t i = 0; i < expr.operands().size(); i++)
      {
        args.emplace_back(
          smt2_symbolt{"op" + std::to_string(i)},
          convert_type(expr.operands()[i].type()));
      }

      exprt tmp1=expr;
      for(std::size_t i = 0; i < tmp1.operands().size(); i++)
        tmp1.operands()[i] = smt2_symbol_exprt(
          "op" + std::to_string(i), tmp1.operands()[i].type());

      exprt tmp2=float_bv(tmp1);
      tmp2=letify(tmp2);
      CHECK_RETURN(!tmp2.is_nil());

      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::define_fun(
          smt2_symbolt{function},
          smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>>(std::move(args)),
          convert_type(expr.type()),
          convert_expr(tmp2))));
    }
  }
  return result;
}

bool smt2_convt::use_array_theory(const exprt &expr)
{
  const typet &type = expr.type();
  PRECONDITION(type.id()==ID_array);

  if(use_datatypes)
  {
    return true; // always use array theory when we have datatypes
  }
  else
  {
    // arrays inside structs get flattened
    if(expr.id()==ID_with)
      return use_array_theory(to_with_expr(expr).old());
    else if(expr.id()==ID_member)
      return false;
    else
      return true;
  }
}

smt2_sortt smt2_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    CHECK_RETURN(array_type.size().is_not_nil());

    // we always use array theory for top-level arrays
    const typet &subtype = array_type.subtype();

    auto subtype_ast = [&] {
      if(subtype.id() == ID_bool && !use_array_of_bool)
        return smt2_sortt::BitVec(1);
      return convert_type(array_type.subtype());
    }();
    return smt2_sortt{
      smt2_identifiert{smt2_symbolt{"Array"}},
      {convert_type(array_type.size().type()), std::move(subtype_ast)}};
  }
  else if(type.id()==ID_bool)
  {
    return smt2_sortt::Bool();
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    if(use_datatypes)
    {
      return smt2_sortt{smt2_symbolt{datatype_map.at(type)}};
    }
    else
    {
      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of struct");
      return smt2_sortt::BitVec(width);
    }
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      return smt2_sortt{smt2_symbolt{datatype_map.at(type)}};
    }
    else
    {
      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of vector");
      return smt2_sortt::BitVec(width);
    }
  }
  else if(type.id()==ID_code)
  {
    // These may appear in structs.
    // We replace this by "Bool" in order to keep the same
    // member count.
    return smt2_sortt::Bool();
  }
  else if(type.id() == ID_union || type.id() == ID_union_tag)
  {
    std::size_t width=boolbv_width(type);
    CHECK_RETURN_WITH_DIAGNOSTICS(width != 0, "failed to get width of union");
    return smt2_sortt::BitVec(width);
  }
  else if(type.id()==ID_pointer)
  {
    return smt2_sortt::BitVec(boolbv_width(type));
  }
  else if(type.id()==ID_bv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_bool)
  {
    return smt2_sortt::BitVec(to_bitvector_type(type).get_width());
  }
  else if(type.id()==ID_c_enum)
  {
    // these have a subtype
    return smt2_sortt::BitVec(to_bitvector_type(type.subtype()).get_width());
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return convert_type(ns.follow_tag(to_c_enum_tag_type(type)));
  }
  else if(type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(type);

    if(use_FPA_theory)
      return smt2_sortt{
        smt2_identifiert{smt2_symbolt("FloatingPoint"),
                         {smt2_constantt::make(floatbv_type.get_e()),
                          smt2_constantt::make(floatbv_type.get_f() + 1)}},
        {}};

    else
      return smt2_sortt::BitVec(floatbv_type.get_width());
  }
  else if(type.id()==ID_rational ||
          type.id()==ID_real)
    return smt2_sortt::Real();
  else if(type.id()==ID_integer)
    return smt2_sortt::Int();
  else if(type.id()==ID_complex)
  {
    if(use_datatypes)
    {
      return smt2_sortt{smt2_symbolt(datatype_map.at(type))};
    }
    else
    {
      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of complex");
      return smt2_sortt::BitVec(width);
    }
  }
  else if(type.id()==ID_c_bit_field)
  {
    return convert_type(
      c_bit_field_replacement_type(to_c_bit_field_type(type), ns));
  }
  else
  {
    UNEXPECTEDCASE("unsupported type: "+type.id_string());
  }
}

std::list<std::unique_ptr<smt2_command_or_commentt>>
smt2_convt::find_symbols(const typet &type)
{
  std::set<irep_idt> recstack;
  return find_symbols_rec(type, recstack);
}

std::list<std::unique_ptr<smt2_command_or_commentt>>
smt2_convt::find_symbols_rec(const typet &type, std::set<irep_idt> &recstack)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    auto result = find_symbols(array_type.size());
    auto rec_result = find_symbols_rec(array_type.subtype(), recstack);
    result.splice(result.end(), rec_result);
    return result;
  }
  else if(type.id()==ID_complex)
  {
    auto result = find_symbols_rec(type.subtype(), recstack);

    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const std::string smt_typename =
        "complex." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;

      // (declare-datatypes () ((smt_typename (mk-smt_typename (
      //  smt_typename.imag type_subtype) (smt_typename.real type_subtype)))))
      result.push_back(util_make_unique<
                       smt2_commandt>(smt2_commandt::declare_datatypes(
        smt2_listt<smt2_datatype_declarationt>{{smt2_datatype_declarationt{
          smt2_non_empty_listt<smt2_symbolt>{smt2_symbolt{smt_typename}, {}},
          smt2_non_empty_listt<smt2_constructor_declarationt>{
            smt2_constructor_declarationt{
              smt2_symbolt{"mk-" + smt_typename},
              {smt2_selector_declarationt{smt2_symbolt{smt_typename + ".imag"},
                                          convert_type(type.subtype())},
               smt2_selector_declarationt{smt2_symbolt{smt_typename + ".real "},
                                          convert_type(type.subtype())}}},
            {}}}}})));
    }
    return result;
  }
  else if(type.id()==ID_vector)
  {
    auto result = find_symbols_rec(type.subtype(), recstack);

    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const vector_typet &vector_type=to_vector_type(type);

      mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

      const std::string smt_typename =
        "vector." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;

      std::vector<smt2_selector_declarationt> selectors;

      for(mp_integer i=0; i!=size; ++i)
      {
        selectors.emplace_back(
          smt2_symbolt{smt_typename + "." + integer2string(i)},
          convert_type(type.subtype()));
      }
      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_datatypes(
          smt2_listt<smt2_datatype_declarationt>{{smt2_datatype_declarationt{
            smt2_non_empty_listt<smt2_symbolt>{smt2_symbolt{smt_typename}, {}},
            smt2_non_empty_listt<smt2_constructor_declarationt>{
              {smt2_constructor_declarationt{smt2_symbolt{"mk-" + smt_typename},
                                             std::move(selectors)}},
              {}}}}})));
    }
    return result;
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

    std::list<std::unique_ptr<smt2_command_or_commentt>> result;
    for(const auto &component : components)
    {
      auto tmp_result = find_symbols_rec(component.type(), recstack);
      result.splice(result.end(), tmp_result);
    }

    // Declare the corresponding SMT type if we haven't already.
    if(need_decl)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // We're going to create a datatype named something like `struct.0'.
      // It's going to have a single constructor named `mk-struct.0' with an
      // argument for each member of the struct.  The declaration that
      // creates this type looks like:
      //
      // (declare-datatypes () ((struct.0 (mk-struct.0
      //                                   (struct.0.component1 type1)
      //                                   ...
      //                                   (struct.0.componentN typeN)))))

      std::vector<smt2_selector_declarationt> selectors;
      for(const auto &component : components)
      {
        selectors.emplace_back(
          smt2_symbolt{smt_typename + "." + id2string(component.get_name())},
          convert_type(component.type()));
      }
      result.push_back(
        util_make_unique<smt2_commandt>(smt2_commandt::declare_datatypes(
          smt2_listt<smt2_datatype_declarationt>{{smt2_datatype_declarationt{
            smt2_non_empty_listt<smt2_symbolt>{smt2_symbolt{smt_typename}, {}},
            smt2_non_empty_listt<smt2_constructor_declarationt>{
              {smt2_constructor_declarationt{smt2_symbolt{"mk-" + smt_typename},
                                             std::move(selectors)}},
              {}}}}})));

      // Let's also declare convenience functions to update individual
      // members of the struct while we're at it.  The functions are
      // named like `update-struct.0.component1'.  Their declarations
      // look like:
      //
      // (define-fun update-struct.0.component1
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
        const struct_union_typet::componentt &component=*it;
        const smt2_symbolt s{"s"};
        const smt2_symbolt v{"v"};
        const smt2_sortt sort{smt2_symbolt{smt_typename}};
        smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>> arguments{
          {smt2_pairt<smt2_symbolt, smt2_sortt>{s, sort},
           smt2_pairt<smt2_symbolt, smt2_sortt>{
             v, convert_type(component.type())}}};

        std::vector<smt2_astt> mk_arguments;
        for(struct_union_typet::componentst::const_iterator it2 =
              components.begin();
            it2 != components.end();
            ++it2)
        {
          if(it==it2)
            mk_arguments.push_back(v);
          else
          {
            mk_arguments.push_back(smt2_function_applicationt{
              smt2_identifiert{
                smt2_symbolt{smt_typename + "." + id2string(it2->get_name())}},
              {s}});
          }
        }

        result.push_back(
          util_make_unique<smt2_commandt>(smt2_commandt::define_fun(
            smt2_symbolt{"update-" + smt_typename + "." +
                         id2string(component.get_name())},
            std::move(arguments),
            smt2_sortt{smt2_symbolt{smt_typename}},
            smt2_function_applicationt{
              smt2_identifiert{smt2_symbolt{"mk-" + smt_typename}},
              std::move(mk_arguments)})));
      }
    }
    return result;
  }
  else if(type.id() == ID_union)
  {
    const union_typet::componentst &components =
      to_union_type(type).components();
    std::list<std::unique_ptr<smt2_command_or_commentt>> result;
    for(const auto &component : components)
    {
      auto tmp_result = find_symbols_rec(component.type(), recstack);
      result.splice(result.end(), tmp_result);
    }
    return result;
  }
  else if(type.id()==ID_code)
  {
    std::list<std::unique_ptr<smt2_command_or_commentt>> result;
    const code_typet::parameterst &parameters=
      to_code_type(type).parameters();
    for(const auto &param : parameters)
    {
      auto tmp_result = find_symbols_rec(param.type(), recstack);
      result.splice(result.end(), tmp_result);
    }

    auto tmp_result =
      find_symbols_rec(to_code_type(type).return_type(), recstack);
    result.splice(result.end(), tmp_result);
    return result;
  }
  else if(type.id()==ID_pointer)
  {
    return find_symbols_rec(type.subtype(), recstack);
  }
  else if(type.id() == ID_struct_tag)
  {
    const auto &struct_tag = to_struct_tag_type(type);
    const irep_idt &id = struct_tag.get_identifier();

    std::list<std::unique_ptr<smt2_command_or_commentt>> result;
    if(recstack.find(id) == recstack.end())
    {
      recstack.insert(id);
      auto tmp_result = find_symbols_rec(ns.follow_tag(struct_tag), recstack);
      result.splice(result.end(), tmp_result);
    }
    return result;
  }
  else if(type.id() == ID_union_tag)
  {
    const auto &union_tag = to_union_tag_type(type);
    const irep_idt &id = union_tag.get_identifier();

    if(recstack.find(id) == recstack.end())
    {
      recstack.insert(id);
      return find_symbols_rec(ns.follow_tag(union_tag), recstack);
    }
  }
  return {};
}

std::size_t smt2_convt::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}
