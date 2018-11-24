/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SMT Backend

#include "smt2_conv.h"

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/fixedbv.h>
#include <util/format_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string2int.h>
#include <util/string_constant.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>
#include <solvers/lowering/expr_lowering.h>

// Mark different kinds of error conditions

// Unexpected types and other combinations not implemented and not
// expected to be needed
#define UNEXPECTEDCASE(S) PRECONDITION_WITH_DIAGNOSTICS(false, S);

// General todos
#define SMT2_TODO(S) PRECONDITION_WITH_DIAGNOSTICS(false, "TODO: " S)

void smt2_convt::print_assignment(std::ostream &out) const
{
  // Boolean stuff

  for(std::size_t v=0; v<boolean_assignment.size(); v++)
    out << "b" << v << "=" << boolean_assignment[v] << "\n";

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

  out << "(set-info :source \"" << notes << "\")" << "\n";

  out << "(set-option :produce-models true)" << "\n";

  // We use a broad mixture of logics, so on some solvers
  // its better not to declare here.
  // set-logic should come after setting options
  if(emit_set_logic && !logic.empty())
    out << "(set-logic " << logic << ")" << "\n";
}

void smt2_convt::write_footer(std::ostream &out)
{
  out << "\n";

  // add the assumptions, if any
  if(!assumptions.empty())
  {
    out << "; assumptions\n";

    forall_literals(it, assumptions)
    {
      out << "(assert ";
      convert_literal(*it);
      out << ")" << "\n";
    }
  }

  // fix up the object sizes
  for(const auto &object : object_sizes)
    define_object_size(object.second, object.first);

  out << "(check-sat)" << "\n";
  out << "\n";

  if(solver!=solvert::BOOLECTOR)
  {
    for(const auto &id : smt2_identifiers)
      out << "(get-value (|" << id << "|))" << "\n";
  }

  out << "\n";

  out << "(exit)\n";

  out << "; end of SMT2 file" << "\n";
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
    const typet &type = ns.follow(o.type());
    exprt size_expr = size_of_expr(type, ns);
    mp_integer object_size;

    if(o.id()!=ID_symbol ||
       size_expr.is_nil() ||
       to_integer(size_expr, object_size))
    {
      ++number;
      continue;
    }

    out << "(assert (implies (= " <<
      "((_ extract " << h << " " << l << ") ";
    convert_expr(ptr);
    out << ") (_ bv" << number << " "
        << config.bv_encoding.object_bits << "))"
        << "(= " << id << " (_ bv" << object_size.to_ulong() << " "
        << size_width << "))))\n";

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

  if(src.id()!=irep_idt())
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
      // stitch the bits together
      std::string bits=id2string(s1.get_value())+
                       id2string(s2.get_value())+
                       id2string(s3.get_value());
      value=binary2integer(bits, false);
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
    return
      from_integer(
        value,
        ns.follow_tag(to_c_enum_tag_type(type)));
  }
  else if(type.id()==ID_fixedbv ||
          type.id()==ID_floatbv)
  {
    std::size_t width=boolbv_width(type);
    return constant_exprt(integer2binary(value, width), type);
  }
  else if(type.id()==ID_integer ||
          type.id()==ID_range)
    return from_integer(value, type);
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

exprt smt2_convt::parse_struct(
  const irept &src,
  const struct_typet &type)
{
  const struct_typet::componentst &components =
    type.components();

  struct_exprt result(type);

  result.operands().resize(components.size(), nil_exprt());

  if(components.empty())
    return std::move(result);

  if(use_datatypes)
  {
    // Structs look like:
    //  (mk-struct.1 <component0> <component1> ... <componentN>)

    if(src.get_sub().size()!=components.size()+1)
      return std::move(result); // give up

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
    exprt l = parse_literal(src, unsignedbv_typet(total_width));
    if(!l.is_constant())
      return nil_exprt();

    irep_idt binary=to_constant_expr(l).get_value();
    if(binary.size()!=total_width)
      return nil_exprt();

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

  return std::move(result);
}

exprt smt2_convt::parse_rec(const irept &src, const typet &_type)
{
  const typet &type=ns.follow(_type);

  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_integer ||
     type.id()==ID_rational ||
     type.id()==ID_real ||
     type.id()==ID_fixedbv ||
     type.id()==ID_floatbv)
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
  else if(type.id()==ID_union)
  {
    return parse_union(src, to_union_type(type));
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
  if(expr.id()==ID_symbol ||
     expr.id()==ID_constant ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_label)
  {
    out
      << "(concat (_ bv"
      << pointer_logic.add_object(expr) << " "
      << config.bv_encoding.object_bits << ")"
      << " (_ bv0 "
      << boolbv_width(result_type)-config.bv_encoding.object_bits << "))";
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
        pointer_type(array.type().subtype()));

      plus_exprt plus_expr(
        address_of_expr,
        index,
        address_of_expr.type());

      convert_expr(plus_expr);
    }
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);

    const exprt &struct_op=member_expr.struct_op();
    const typet &struct_op_type=ns.follow(struct_op.type());

    DATA_INVARIANT(
      struct_op_type.id() == ID_struct,
      "member expression operand shall have struct type");

    const struct_typet &struct_type = to_struct_type(struct_op_type);

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

void smt2_convt::convert_byte_extract(const byte_extract_exprt &expr)
{
  // we just run the flattener
  exprt flattened_expr=flatten_byte_extract(expr, ns);
  unflatten(wheret::BEGIN, expr.type());
  convert_expr(flattened_expr);
  unflatten(wheret::END, expr.type());
}

void smt2_convt::convert_byte_update(const byte_update_exprt &expr)
{
  #if 0
  // The situation: expr.op0 needs to be split in 3 parts
  // |<--- L --->|<--- M --->|<--- R --->|
  // where M is the expr.op1'th byte
  // We need to output L expr.op2 R

  mp_integer i = numeric_cast_v<mp_integer>(expr.op());

  std::size_t total_width=boolbv_width(expr.op().type());
  CHECK_RETURN_WITH_DIAGNOSTICS(
    total_width != 0,
    "failed to get width of byte_update");

  std::size_t value_width=boolbv_width(expr.value().type());

  mp_integer upper, lower; // of the byte
  mp_integer max=total_width-1;

  if(expr.id()==ID_byte_update_little_endian)
  {
    lower = i*8;
    upper = lower+value_width-1;
  }
  else if(expr.id()==ID_byte_update_big_endian)
  {
    upper = max-(i*8);
    lower = max-((i+1)*8-1);
  }
  else
    UNEXPECTEDCASE("byte update neither big nor little endian");

  unflatten(BEGIN, expr.type());

  if(upper==max)
  {
    if(lower==0) // the update expression is expr.value()
    {
      flatten2bv(expr.value());
    }
    else // uppermost byte selected, only R needed
    {
      out << "(concat ";
      flatten2bv(expr.value());
      out << " ((_ extract " << lower-1 << " 0) ";
      flatten2bv(expr.op());
      out << "))";
    }
  }
  else
  {
    if(lower==0) // lowermost byte selected, only L needed
    {
      out << "(concat ";
      out << "((_ extract " << max << " " << (upper+1) << ") ";
      flatten2bv(expr.op());
      out << ") ";
      flatten2bv(expr.value());
      out << ")";
    }
    else // byte in the middle selected, L & R needed
    {
      out << "(concat (concat ";
      out << "((_ extract " << max << " " << (upper+1) << ") ";
      flatten2bv(expr.op());
      out << ") ";
      flatten2bv(expr.value());
      out << ") ((_ extract " << (lower-1) << " 0) ";
      flatten2bv(expr.op());
      out << "))";
    }
  }

  unflatten(END, expr.type());

  #else

  // We'll do an AND-mask for op(), and then OR-in
  // the value() shifted by the offset * 8.

  std::size_t total_width=boolbv_width(expr.op().type());
  std::size_t value_width=boolbv_width(expr.value().type());

  mp_integer mask=power(2, value_width)-1;
  exprt one_mask=from_integer(mask, unsignedbv_typet(total_width));

  const mult_exprt distance(
    expr.offset(), from_integer(8, expr.offset().type()));

  const bitand_exprt and_expr(expr.op(), bitnot_exprt(one_mask));
  const typecast_exprt ext_value(expr.value(), one_mask.type());
  const bitor_exprt or_expr(and_expr, shl_exprt(ext_value, distance));

  unflatten(wheret::BEGIN, expr.type());
  flatten2bv(or_expr);
  unflatten(wheret::END, expr.type());
  #endif
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

  find_symbols(expr);

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;

  out << "; convert\n";
  out << "(define-fun ";
  convert_literal(l);
  out << " () Bool ";
  convert_expr(expr);
  out << ")" << "\n";

  return l;
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

    out << "|B" << l.var_no() << "|";

    if(l.sign())
      out << ")";

    smt2_identifiers.insert("B"+std::to_string(l.var_no()));
  }
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
  else
  {
    UNREACHABLE;
    return "";
  }
}

std::string smt2_convt::floatbv_suffix(const exprt &expr) const
{
  PRECONDITION(!expr.operands().empty());
  return "_"+type2id(expr.op0().type())+"->"+type2id(expr.type());
}

void smt2_convt::convert_floatbv(const exprt &expr)
{
  PRECONDITION(!use_FPA_theory);

  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    out << '|' << convert_identifier(id) << '|';
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

  out << "(|float_bv." << expr.id()
      << floatbv_suffix(expr)
      << '|';

  forall_operands(it, expr)
  {
    out << ' ';
    convert_expr(*it);
  }

  out << ')';
}

void smt2_convt::convert_expr(const exprt &expr)
{
  // huge monster case split over expression id
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "symbol must have identifier");
    out << '|' << convert_identifier(id) << '|';
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id = to_nondet_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "nondet symbol must have identifier");
    out << '|' << convert_identifier("nondet_"+id2string(id)) << '|';
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
  else if(expr.id()==ID_constant)
  {
    convert_constant(to_constant_expr(expr));
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

    forall_operands(it, expr)
    {
      out << " ";
      flatten2bv(*it);
    }

    out << ")";
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

        out << "(let ((?vectorop ";
        convert_expr(bitnot_expr.op());
        out << ")) ";

        out << "(mk-" << smt_typename;

        typet index_type=vector_type.size().type();

        // do bitnot component-by-component
        for(mp_integer i=0; i!=size; ++i)
        {
          out << " (bvnot (" << smt_typename << "." << (size-i-1)
              << " ?vectorop))";
        }

        out << "))"; // mk-, let
      }
      else
        SMT2_TODO("bitnot for vectors");
    }
    else
    {
      out << "(bvnot ";
      convert_expr(bitnot_expr.op());
      out << ")";
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

        out << "(let ((?vectorop ";
        convert_expr(unary_minus_expr.op());
        out << ")) ";

        out << "(mk-" << smt_typename;

        typet index_type=vector_type.size().type();

        // negate component-by-component
        for(mp_integer i=0; i!=size; ++i)
        {
          out << " (bvneg (" << smt_typename << "." << (size-i-1)
              << " ?vectorop))";
        }

        out << "))"; // mk-, let
      }
      else
        SMT2_TODO("unary minus for vector");
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
      expr.type().id() == ID_bool,
      "logical and, or, and xor expressions should have Boolean type");
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions should have at least two operands");

    out << "(" << expr.id();
    forall_operands(it, expr)
    {
      out << " ";
      convert_expr(*it);
    }
    out << ")";
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);

    DATA_INVARIANT(
      implies_expr.type().id() == ID_bool,
      "implies expression should have Boolean type");

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
      not_expr.type().id() == ID_bool,
      "not expression should have Boolean type");

    out << "(not ";
    convert_expr(not_expr.op());
    out << ")";
  }
  else if(expr.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(expr);

    DATA_INVARIANT(
      base_type_eq(equal_expr.op0().type(), equal_expr.op1().type(), ns),
      "operands of equal expression shall have same type");

    out << "(= ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.id() == ID_notequal)
  {
    const notequal_exprt &notequal_expr = to_notequal_expr(expr);

    DATA_INVARIANT(
      base_type_eq(notequal_expr.op0().type(), notequal_expr.op1().type(), ns),
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
    DATA_INVARIANT(
      expr.operands().size() == 2,
      "float equal and not equal expressions must have two operands");
    DATA_INVARIANT(
      base_type_eq(expr.op0().type(), expr.op1().type(), ns),
      "operands of float equal and not equal expressions shall have same type");

    // The FPA theory properly treats NaN and negative zero.
    if(use_FPA_theory)
    {
      if(expr.id()==ID_ieee_float_notequal)
        out << "(not ";

      out << "(fp.eq ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";

      if(expr.id()==ID_ieee_float_notequal)
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
    convert_relation(expr);
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
  else if(expr.id()==ID_mult)
  {
    convert_mult(to_mult_expr(expr));
  }
  else if(expr.id()==ID_floatbv_mult)
  {
    convert_floatbv_mult(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr = to_address_of_expr(expr);
    convert_address_of_rec(
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
    out << it->second;
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
        mp_integer i = numeric_cast_v<mp_integer>(shift_expr.distance());

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
  else if(expr.id()==ID_with)
  {
    convert_with(to_with_expr(expr));
  }
  else if(expr.id()==ID_update)
  {
    convert_update(expr);
  }
  else if(expr.id()==ID_member)
  {
    convert_member(to_member_expr(expr));
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

    // too few bits?
    if(result_width>offset_bits)
      out << "((_ zero_extend " << result_width-offset_bits << ") ";

    out << "((_ extract " << offset_bits-1 << " 0) ";
    convert_expr(expr.op0());
    out << ")";

    if(result_width>offset_bits)
      out << ")"; // zero_extend
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

    if(ext>0)
      out << "((_ zero_extend " << ext << ") ";

    out << "((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(expr.op0());
    out << ")";

    if(ext>0)
      out << ")"; // zero_extend
  }
  else if(expr.id()==ID_dynamic_object)
  {
    convert_is_dynamic_object(expr);
  }
  else if(expr.id()==ID_invalid_pointer)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1,
      "invalid pointer expression shall have one operand");

    std::size_t pointer_width=boolbv_width(expr.op0().type());
    out << "(= ((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(expr.op0());
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

    if(expr.op1().is_constant())
    {
      mp_integer i = numeric_cast_v<mp_integer>(extractbit_expr.index());

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
      typecast_exprt tmp(extractbit_expr.src().type());
      tmp.op0() = extractbit_expr.index();
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
      mp_integer op1_i = numeric_cast_v<mp_integer>(extractbits_expr.upper());
      mp_integer op2_i = numeric_cast_v<mp_integer>(extractbits_expr.lower());

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
    convert_byte_extract(to_byte_extract_expr(expr));
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    convert_byte_update(to_byte_update_expr(expr));
  }
  else if(expr.id()==ID_width)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "width expression should have one operand");

    boolbv_widtht boolbv_width(ns);

    std::size_t result_width=boolbv_width(expr.type());
    CHECK_RETURN(result_width != 0);

    std::size_t op_width=boolbv_width(expr.op0().type());
    CHECK_RETURN(op_width != 0);

    out << "(_ bv" << op_width/8
        << " " << result_width << ")";
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

        out << "(not (fp.isInf ";
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
      out << "(let ((?sum (";
      out << (subtract?"bvsub":"bvadd");
      out << " ((_ sign_extend 1) ";
      convert_expr(expr.op0());
      out << ")";
      out << " ((_ sign_extend 1) ";
      convert_expr(expr.op1());
      out << ")))) "; // sign_extend, bvadd/sub let2
      out << "(not (= "
                   "((_ extract " << width << " " << width << ") ?sum) "
                   "((_ extract " << (width-1) << " " << (width-1) << ") ?sum)";
      out << ")))"; // =, not, let
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_pointer)
    {
      // overflow is simply carry-out
      out << "(= ";
      out << "((_ extract " << width << " " << width << ") ";
      out << "(" << (subtract?"bvsub":"bvadd");
      out << " ((_ zero_extend 1) ";
      convert_expr(expr.op0());
      out << ")";
      out << " ((_ zero_extend 1) ";
      convert_expr(expr.op1());
      out << ")))"; // zero_extend, bvsub/bvadd, extract
      out << " #b1)"; // =
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "overflow check should not be performed on unsupported type",
        op_type.id_string());
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
      out << "(let ( (prod (bvmul ((_ sign_extend " << width << ") ";
      convert_expr(expr.op0());
      out << ") ((_ sign_extend " << width << ") ";
      convert_expr(expr.op1());
      out << ")) )) ";
      out << "(or (bvsge prod (_ bv" << power(2, width-1) << " "
          << width*2 << "))";
      out << " (bvslt prod (bvneg (_ bv" << power(2, width-1) << " "
          << width*2 << ")))))";
    }
    else if(op_type.id()==ID_unsignedbv)
    {
      out << "(bvuge (bvmul ((_ zero_extend " << width << ") ";
      convert_expr(expr.op0());
      out << ") ((_ zero_extend " << width << ") ";
      convert_expr(expr.op1());
      out << ")) (_ bv" << power(2, width) << " " << width*2 << "))";
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

    exprt bound=expr.op0();

    out << "((";
    convert_expr(bound);
    out << " ";
    convert_type(bound.type());
    out << ")) ";

    convert_expr(quantifier_expr.where());

    out << ")";
  }
  else if(expr.id()==ID_vector)
  {
    const vector_exprt &vector_expr = to_vector_expr(expr);
    const vector_typet &vector_type = to_vector_type(vector_expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    DATA_INVARIANT(
      size == vector_expr.operands().size(),
      "size indicated by type shall be equal to the number of operands");

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(vector_type);

      out << "(mk-" << smt_typename;
    }
    else
      out << "(concat";

    // build component-by-component
    forall_operands(it, vector_expr)
    {
      out << " ";
      convert_expr(*it);
    }

    out << ")"; // mk-... or concat
  }
  else if(expr.id()==ID_object_size)
  {
    out << object_sizes[expr];
  }
  else if(expr.id()==ID_let)
  {
    const let_exprt &let_expr=to_let_expr(expr);
    out << "(let ((";
    convert_expr(let_expr.symbol());
    out << ' ';
    convert_expr(let_expr.value());
    out << ")) ";
    convert_expr(let_expr.where());
    out << ')'; // let
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
    exprt lowered = lower_popcount(to_popcount_expr(expr), ns);
    convert_expr(lowered);
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

  typet dest_type=ns.follow(expr.type());
  if(dest_type.id()==ID_c_enum_tag)
    dest_type=ns.follow_tag(to_c_enum_tag_type(dest_type));

  typet src_type=ns.follow(src.type());
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
    out << ")) "; // not, =
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

      // some faction bit is not zero
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
          // This conversion is non-trivial as it requires creating a
          // new bit-vector variable and then asserting that it converts
          // to the required floating-point number.
          SMT2_TODO("bit-wise floatbv to bv");
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
        mp_integer i = numeric_cast_v<mp_integer>(src);
        out << "(_ bv" << i << " " << to_width << ")";
      }
      else
        SMT2_TODO("can't convert non-constant integer to bitvector");
    }
    else if(src_type.id()==ID_struct) // flatten a struct to a bit-vector
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
    else if(src_type.id()==ID_union) // flatten a union
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
    else if(src_type.id()==ID_unsignedbv ||
            src_type.id()==ID_signedbv)
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

    if(src_type.id()==ID_bool)
    {
      constant_exprt val(irep_idt(), dest_type);

      ieee_floatt a(to_floatbv_type(dest_type));

      mp_integer significand;
      mp_integer exponent;

      out << "(ite ";
      convert_expr(src);
      out << " ";

      significand = 1;
      exponent = 0;
      a.build(significand, exponent);
      val.set(ID_value, integer2binary(a.pack(), a.spec.width()));

      convert_constant(val);
      out << " ";

      significand = 0;
      exponent = 0;
      a.build(significand, exponent);
      val.set(ID_value, integer2binary(a.pack(), a.spec.width()));

      convert_constant(val);
      out << ")";
    }
    else if(src_type.id()==ID_c_bool)
    {
      // turn into proper bool
      const typecast_exprt tmp(src, bool_typet());
      convert_typecast(typecast_exprt(tmp, dest_type));
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
      tmp.op()=
        typecast_exprt(
          src,
          ns.follow_tag(to_c_enum_tag_type(src_type)).subtype());
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
  const struct_typet &struct_type=to_struct_type(expr.type());

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
      out << " ";
      convert_expr(expr.operands()[i]);
    }

    out << ")";
  }
  else
  {
    if(components.size()==1)
      convert_expr(expr.op0());
    else
    {
      // SMT-LIB 2 concat is binary only
      for(std::size_t i=components.size(); i>1; i--)
      {
        out << "(concat ";

        exprt op=expr.operands()[i-1];

        // may need to flatten array-theory arrays in there
        if(ns.follow(op.type()).id()==ID_array)
          flatten_array(op);
        else
          convert_expr(op);

        out << " ";
      }

      convert_expr(expr.op0());

      for(std::size_t i=1; i<components.size(); i++)
        out << ")";
    }
  }
}

/// produce a flat bit-vector for a given array of fixed size
void smt2_convt::flatten_array(const exprt &expr)
{
  const array_typet &array_type=
    to_array_type(ns.follow(expr.type()));

  mp_integer size = numeric_cast_v<mp_integer>(array_type.size());
  CHECK_RETURN_WITH_DIAGNOSTICS(size != 0, "can't convert zero-sized array");

  out << "(let ((?far ";
  convert_expr(expr);
  out << ")) ";

  for(mp_integer i=size; i!=0; --i)
  {
    if(i!=1)
      out << "(concat ";
    out << "(select ?far ";
    convert_expr(from_integer(i-1, array_type.size().type()));
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
  const union_typet &union_type=to_union_type(expr.type());
  const exprt &op=expr.op();

  boolbv_widtht boolbv_width(ns);

  std::size_t total_width=boolbv_width(union_type);
  CHECK_RETURN_WITH_DIAGNOSTICS(
    total_width != 0, "failed to get union width for union");

  std::size_t member_width=boolbv_width(op.type());
  CHECK_RETURN_WITH_DIAGNOSTICS(
    member_width != 0, "failed to get union member width for union");

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
     expr_type.id()==ID_incomplete_c_enum ||
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
      ieee_float_spect spec(floatbv_type);

      mp_integer v=binary2integer(
        id2string(expr.get_value()), false);

      out << "(_ bv" << v << " " << spec.width() << ")";
    }
  }
  else if(expr_type.id()==ID_pointer)
  {
    const irep_idt &value=expr.get(ID_value);

    if(value==ID_NULL)
    {
      out << "(_ bv0 " << boolbv_width(expr_type)
          << ")";
    }
    else
      UNEXPECTEDCASE("unknown pointer constant: "+id2string(value));
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
    size_t pos=value.find("/");

    if(pos==std::string::npos)
      out << value << ".0";
    else
    {
      out << "(/ " << value.substr(0, pos) << ".0 "
                   << value.substr(pos+1) << ".0)";
    }
  }
  else if(expr_type.id()==ID_integer)
  {
    out << expr.get_value();
  }
  else
    UNEXPECTEDCASE("unknown constant: "+expr_type.id_string());
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

void smt2_convt::convert_is_dynamic_object(const exprt &expr)
{
  std::vector<std::size_t> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  DATA_INVARIANT(
    expr.operands().size() == 1,
    "is_dynamic_object expression should have one operand");

  if(dynamic_objects.empty())
    out << "false";
  else
  {
    std::size_t pointer_width=boolbv_width(expr.op0().type());

    out << "(let ((?obj ((_ extract "
        << pointer_width-1 << " "
        << pointer_width-config.bv_encoding.object_bits << ") ";
    convert_expr(expr.op0());
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

void smt2_convt::convert_relation(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 2);

  const typet &op_type=expr.op0().type();

  if(op_type.id()==ID_unsignedbv ||
     op_type.id()==ID_pointer ||
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

      const auto element_size = pointer_offset_size(expr.type().subtype(), ns);
      CHECK_RETURN(element_size.has_value() && *element_size >= 1);

      out << "(bvadd ";
      convert_expr(p);
      out << " ";

      if(*element_size >= 2)
      {
        out << "(bvmul ";
        convert_expr(i);
        out << " (_ bv" << *element_size << " " << boolbv_width(expr.type())
            << "))";
      }
      else
        convert_expr(i);

      out << ')';
    }
    else
    {
      convert_plus(to_plus_expr(make_binary(expr)));
    }
  }
  else if(expr.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    typet index_type = vector_type.size().type();

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(vector_type);

      out << "(mk-" << smt_typename;
    }
    else
      out << "(concat";

    // add component-by-component
    for(mp_integer i = 0; i != size; ++i)
    {
      plus_exprt tmp(vector_type.subtype());
      forall_operands(it, expr)
        tmp.copy_to_operands(
          index_exprt(
            *it,
            from_integer(size - i - 1, index_type),
            vector_type.subtype()));

      out << " ";
      convert_expr(tmp);
    }

    out << ")"; // mk-... or concat
  }
  else
    UNEXPECTEDCASE("unsupported type for +: " + expr.type().id_string());
}

/// Converting a constant or symbolic rounding mode to SMT-LIB. Only called when
/// use_FPA_theory is enabled
/// \par parameters: The expression representing the rounding mode.
/// \return SMT-LIB output to out.
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

  if(expr.id()==ID_constant)
  {
    const constant_exprt &cexpr=to_constant_expr(expr);

    mp_integer value=binary2integer(id2string(cexpr.get_value()), false);

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
    (type.id() == ID_complex && type.subtype().id() == ID_floatbv) ||
    (type.id() == ID_vector && type.subtype().id() == ID_floatbv));

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
      auto element_size = pointer_offset_size(expr.op0().type().subtype(), ns);
      CHECK_RETURN(element_size.has_value() && *element_size >= 1);

      if(*element_size >= 2)
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

      if(*element_size >= 2)
        out << " (_ bv" << *element_size << " " << boolbv_width(expr.type())
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
    SMT2_TODO("pointer subtraction");
  }
  else if(expr.type().id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    typet index_type=vector_type.size().type();

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(vector_type);

      out << "(mk-" << smt_typename;
    }
    else
      out << "(concat";

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

      out << " ";
      convert_expr(tmp);
    }

    out << ")"; // mk-... or concat
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
    convert_rounding_mode_FPA(expr.op2());
    out << " ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
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

    forall_operands(it, expr)
    {
      out << " ";
      convert_expr(*it);
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

void smt2_convt::convert_with(const with_exprt &expr)
{
  // get rid of "with" that has more than three operands

  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();

    // strip of the trailing two operands
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

  const typet &expr_type=ns.follow(expr.type());

  if(expr_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(expr_type);

    if(use_array_theory(expr))
    {
      out << "(store ";
      convert_expr(expr.old());
      out << " ";
      convert_expr(typecast_exprt(expr.where(), array_type.size().type()));
      out << " ";
      convert_expr(expr.new_value());
      out << ")";
    }
    else
    {
      // fixed-width
      std::size_t array_width=boolbv_width(array_type);
      std::size_t sub_width=boolbv_width(array_type.subtype());
      std::size_t index_width=boolbv_width(expr.where().type());

      // We mask out the updated bit with AND,
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
      out << "(bvlshr (_ bv" << power(2, array_width)-1 << " "
          << array_width << ") ";
      out << "distance?) ";
      convert_expr(expr.old());
      out << ") "; // bvand
      out << "(bvlshr ";
      out << "((_ zero_extend " << array_width-sub_width << ") ";
      convert_expr(expr.new_value());
      out << ") distance?)))"; // zero_extend, bvlshr, bvor, let
    }
  }
  else if(expr_type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(expr_type);

    const exprt &index=expr.op1();
    const exprt &value=expr.op2();

    const irep_idt &component_name=index.get(ID_component_name);

    INVARIANT(
      struct_type.has_component(component_name),
      "struct should have accessed component");

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(expr_type);

      out << "(update-" << smt_typename << "." << component_name << " ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(value);
      out << ")";
    }
    else
    {
      std::size_t struct_width=boolbv_width(struct_type);

      // figure out the offset and width of the member
      boolbv_widtht::membert m=
        boolbv_width.get_member(struct_type, component_name);

      out << "(let ((?withop ";
      convert_expr(expr.op0());
      out << ")) ";

      if(m.width==struct_width)
      {
        // the struct is the same as the member, no concat needed
        out << "?withop";
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
        out << "((_ extract " << (m.offset-1) << " 0) ?withop))";
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
  else if(expr_type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(expr_type);

    const exprt &value=expr.op2();

    boolbv_widtht boolbv_width(ns);

    std::size_t total_width=boolbv_width(union_type);
    CHECK_RETURN_WITH_DIAGNOSTICS(
      total_width != 0, "failed to get union width for with");

    std::size_t member_width=boolbv_width(value.type());
    CHECK_RETURN_WITH_DIAGNOSTICS(
      member_width != 0, "failed to get union member width for with");

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
      convert_expr(expr.op0());
      out << ") ";
      flatten2bv(value);
      out << ")";
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

void smt2_convt::convert_update(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  SMT2_TODO("smt2_convt::convert_update to be implemented");
}

void smt2_convt::convert_index(const index_exprt &expr)
{
  const typet &array_op_type=ns.follow(expr.array().type());

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(array_op_type);

    if(use_array_theory(expr.array()))
    {
      if(ns.follow(expr.type()).id()==ID_bool && !use_array_of_bool)
      {
        out << "(= ";
        out << "(select ";
        convert_expr(expr.array());
        out << " ";
        convert_expr(typecast_exprt(expr.index(), array_type.size().type()));
        out << ")";
        out << " #b1 #b0)";
      }
      else
      {
        out << "(select ";
        convert_expr(expr.array());
        out << " ";
        convert_expr(typecast_exprt(expr.index(), array_type.size().type()));
        out << ")";
      }
    }
    else
    {
      // fixed size
      std::size_t array_width=boolbv_width(array_type);
      CHECK_RETURN(array_width != 0);

      unflatten(wheret::BEGIN, array_type.subtype());

      std::size_t sub_width=boolbv_width(array_type.subtype());
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

      unflatten(wheret::END, array_type.subtype());
    }
  }
  else if(array_op_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(array_op_type);

    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(vector_type);

      // this is easy for constant indicies

      mp_integer index_int;
      if(to_integer(expr.index(), index_int))
      {
        SMT2_TODO("non-constant index on vectors");
      }
      else
      {
        out << "(" << smt_typename << "." << index_int << " ";
        convert_expr(expr.array());
        out << ")";
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

void smt2_convt::convert_member(const member_exprt &expr)
{
  const member_exprt &member_expr=to_member_expr(expr);
  const exprt &struct_op=member_expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());
  const irep_idt &name=member_expr.get_component_name();

  if(struct_op_type.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(struct_op_type);

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
      std::size_t member_width=boolbv_width(expr.type());
      const auto member_offset = ::member_offset(struct_type, name, ns);

      CHECK_RETURN_WITH_DIAGNOSTICS(
        member_offset.has_value(), "failed to get struct member offset");

      out << "((_ extract " << ((*member_offset) * 8 + member_width - 1) << " "
          << (*member_offset) * 8 << ") ";
      convert_expr(struct_op);
      out << ")";
    }
  }
  else if(struct_op_type.id()==ID_union)
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
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_bool)
  {
    out << "(ite ";
    convert_expr(expr); // this returns a Bool
    out << " #b1 #b0)"; // this is a one-bit bit-vector
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // concatenate elements
      const vector_typet &vector_type=to_vector_type(type);

      mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

      out << "(let ((?vflop ";
      convert_expr(expr);
      out << ")) ";

      out << "(concat";

      for(mp_integer i=0; i!=size; ++i)
      {
        out << " (" << smt_typename << "." << i << " ?vflop)";
      }

      out << "))"; // concat, let
    }
    else
      convert_expr(expr); // already a bv
  }
  else if(type.id()==ID_array)
  {
    convert_expr(expr);
  }
  else if(type.id()==ID_struct)
  {
    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // concatenate elements
      const struct_typet &struct_type=to_struct_type(type);

      out << "(let ((?sflop ";
      convert_expr(expr);
      out << ")) ";

      const struct_typet::componentst &components=
        struct_type.components();

      // SMT-LIB 2 concat is binary only
      for(std::size_t i=components.size(); i>1; i--)
      {
        out << "(concat (" << smt_typename << "."
            << components[i-1].get_name() << " ?sflop)";

        out << " ";
      }

      out << "(" << smt_typename << "."
          << components[0].get_name() << " ?sflop)";

      for(std::size_t i=1; i<components.size(); i++)
        out << ")"; // concat

      out << ")"; // let
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
  if(type.id() == ID_symbol_type)
    return unflatten(where, ns.follow(type));

  if(type.id()==ID_bool)
  {
    if(where==wheret::BEGIN)
      out << "(= "; // produces a bool
    else
      out << " #b1)";
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      const std::string &smt_typename = datatype_map.at(type);

      // extract elements
      const vector_typet &vector_type=to_vector_type(type);

      std::size_t subtype_width=boolbv_width(vector_type.subtype());

      mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

      if(where==wheret::BEGIN)
        out << "(let ((?ufop" << nesting << " ";
      else
      {
        out << ")) ";

        out << "(mk-" << smt_typename;

        std::size_t offset=0;

        for(mp_integer i=0; i!=size; ++i, offset+=subtype_width)
        {
          out << " ";
          unflatten(wheret::BEGIN, vector_type.subtype(), nesting+1);
          out << "((_ extract " << offset+subtype_width-1 << " "
              << offset << ") ?ufop" << nesting << ")";
          unflatten(wheret::END, vector_type.subtype(), nesting+1);
        }

        out << "))"; // mk-, let
      }
    }
    else
    {
      // nop, already a bv
    }
  }
  else if(type.id()==ID_struct)
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

        const struct_typet &struct_type=to_struct_type(type);

        const struct_typet::componentst &components=
          struct_type.components();

        std::size_t offset=0;

        std::size_t i=0;
        for(struct_typet::componentst::const_iterator
            it=components.begin();
            it!=components.end();
            it++, i++)
        {
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

void smt2_convt::convert_overflow(const exprt &)
{
  UNREACHABLE;
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
        find_symbols(id.type);
        find_symbols(equal_expr.rhs());

        std::string smt2_identifier=convert_identifier(identifier);
        smt2_identifiers.insert(smt2_identifier);

        out << "; set_to true (equal)\n";
        out << "(define-fun |" << smt2_identifier << "| () ";

        convert_type(equal_expr.lhs().type());
        out << " ";
        convert_expr(equal_expr.rhs());

        out << ")" << "\n";
        return; // done
      }
    }
  }

  find_symbols(expr);

  #if 0
  out << "; CONV: "
      << format(expr) << "\n";
  #endif

  out << "; set_to " << (value?"true":"false") << "\n"
      << "(assert ";

  if(!value)
  {
    out << "(not ";
    convert_expr(expr);
    out << ")";
  }
  else
    convert_expr(expr);

  out << ")" << "\n"; // assert

  return;
}

void smt2_convt::find_symbols(const exprt &expr)
{
  // recursive call on type
  find_symbols(expr.type());

  // recursive call on operands
  forall_operands(it, expr)
    find_symbols(*it);

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
      out << "(declare-fun |"
          << smt2_identifier
          << "| () ";
      convert_type(expr.type());
      out << ")" << "\n";
    }
  }
  else if(expr.id()==ID_array_of)
  {
    if(defined_expressions.find(expr)==defined_expressions.end())
    {
      const irep_idt id =
        "array_of." + std::to_string(defined_expressions.size());
      out << "; the following is a substitute for lambda i. x" << "\n";
      out << "(declare-fun " << id << " () ";
      convert_type(expr.type());
      out << ")" << "\n";

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
      out << "; the following is a substitute for an array constructor" << "\n";
      out << "(declare-fun " << id << " () ";
      convert_type(array_type);
      out << ")" << "\n";

      for(std::size_t i=0; i<expr.operands().size(); i++)
      {
        out << "(assert (= (select " << id << " ";
        convert_expr(from_integer(i, array_type.size().type()));
        out << ") "; // select
        convert_expr(expr.operands()[i]);
        out << "))" << "\n"; // =, assert
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
        out << "(assert (= (select " << id;
        convert_expr(from_integer(i, array_type.size().type()));
        out << ") "; // select
        convert_expr(tmp.operands()[i]);
        out << "))" << "\n";
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
        out << "(declare-fun " << id << " () ";
        convert_type(expr.type());
        out << ")" << "\n";

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
      out << "; this is a model for " << expr.id()
          << " : " << type2id(expr.op0().type())
          << " -> " << type2id(expr.type()) << "\n"
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
}

bool smt2_convt::use_array_theory(const exprt &expr)
{
  const typet &type=ns.follow(expr.type());
  PRECONDITION(type.id()==ID_array);
  // const array_typet &array_type=to_array_type(ns.follow(expr.type()));

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

void smt2_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    CHECK_RETURN(array_type.size().is_not_nil());

    // we always use array theory for top-level arrays
    const typet &subtype=ns.follow(array_type.subtype());

    out << "(Array ";
    convert_type(array_type.size().type());
    out << " ";

    if(subtype.id()==ID_bool && !use_array_of_bool)
      out << "(_ BitVec 1)";
    else
      convert_type(array_type.subtype());

    out << ")";
  }
  else if(type.id()==ID_bool)
  {
    out << "Bool";
  }
  else if(type.id()==ID_struct)
  {
    if(use_datatypes)
    {
      out << datatype_map.at(type);
    }
    else
    {
      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of struct");

      out << "(_ BitVec " << width << ")";
    }
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      out << datatype_map.at(type);
    }
    else
    {
      boolbv_widtht boolbv_width(ns);

      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of vector");

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
  else if(type.id()==ID_union)
  {
    boolbv_widtht boolbv_width(ns);

    std::size_t width=boolbv_width(type);
    CHECK_RETURN_WITH_DIAGNOSTICS(width != 0, "failed to get width of union");

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
    // these have a subtype
    out << "(_ BitVec "
        << to_bitvector_type(type.subtype()).get_width() << ")";
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
  else if(type.id() == ID_symbol_type)
    convert_type(ns.follow(type));
  else if(type.id()==ID_complex)
  {
    if(use_datatypes)
    {
      out << datatype_map.at(type);
    }
    else
    {
      boolbv_widtht boolbv_width(ns);

      std::size_t width=boolbv_width(type);
      CHECK_RETURN_WITH_DIAGNOSTICS(
        width != 0, "failed to get width of complex");

      out << "(_ BitVec " << width << ")";
    }
  }
  else if(type.id()==ID_c_bit_field)
  {
    convert_type(c_bit_field_replacement_type(to_c_bit_field_type(type), ns));
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
    find_symbols_rec(array_type.subtype(), recstack);
  }
  else if(type.id()==ID_incomplete_array)
  {
    find_symbols_rec(type.subtype(), recstack);
  }
  else if(type.id()==ID_complex)
  {
    find_symbols_rec(type.subtype(), recstack);

    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const std::string smt_typename =
        "complex." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;

      out << "(declare-datatypes () ((" << smt_typename << " "
          << "(mk-" << smt_typename;

      out << " (" << smt_typename << ".imag ";
      convert_type(type.subtype());
      out << ")";

      out << " (" << smt_typename << ".real ";
      convert_type(type.subtype());
      out << ")";

      out << "))))\n";
    }
  }
  else if(type.id()==ID_vector)
  {
    find_symbols_rec(type.subtype(), recstack);

    if(use_datatypes &&
       datatype_map.find(type)==datatype_map.end())
    {
      const vector_typet &vector_type=to_vector_type(type);

      mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

      const std::string smt_typename =
        "vector." + std::to_string(datatype_map.size());
      datatype_map[type] = smt_typename;

      out << "(declare-datatypes () ((" << smt_typename << " "
          << "(mk-" << smt_typename;

      for(mp_integer i=0; i!=size; ++i)
      {
        out << " (" << smt_typename << "." << i << " ";
        convert_type(type.subtype());
        out << ")";
      }

      out << "))))\n";
    }
  }
  else if(type.id()==ID_struct)
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

    const struct_typet::componentst &components=
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
      // (declare-datatypes () ((struct.0 (mk-struct.0
      //                                   (struct.0.component1 type1)
      //                                   ...
      //                                   (struct.0.componentN typeN)))))
      out << "(declare-datatypes () ((" << smt_typename << " "
          << "(mk-" << smt_typename << " ";

      for(const auto &component : components)
      {
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
          else
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
  else if(type.id()==ID_union)
  {
    const union_typet::componentst &components=
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
    find_symbols_rec(type.subtype(), recstack);
  }
  else if(type.id() == ID_symbol_type)
  {
    const symbol_typet &st=to_symbol_type(type);
    const irep_idt &id=st.get_identifier();

    if(recstack.find(id)==recstack.end())
    {
      recstack.insert(id);
      find_symbols_rec(ns.follow(type), recstack);
    }
  }
}

exprt smt2_convt::letify(exprt &expr)
{
  seen_expressionst map;
  std::vector<exprt> let_order;

  collect_bindings(expr, map, let_order);

  return letify_rec(expr, let_order, map, 0);
}

exprt smt2_convt::letify_rec(
  exprt &expr,
  std::vector<exprt> &let_order,
  const seen_expressionst &map,
  std::size_t i)
{
  if(i>=let_order.size())
    return substitute_let(expr, map);

  exprt current=let_order[i];
  INVARIANT(
    map.find(current) != map.end(), "expression should have been seen already");

  if(map.find(current)->second.count < LET_COUNT)
    return letify_rec(expr, let_order, map, i+1);

  return let_exprt(
    map.find(current)->second.let_symbol,
    substitute_let(current, map),
    letify_rec(expr, let_order, map, i + 1));
}

void smt2_convt::collect_bindings(
  exprt &expr,
  seen_expressionst &map,
  std::vector<exprt> &let_order)
{
  seen_expressionst::iterator it = map.find(expr);

  if(it!=map.end())
  {
    let_count_idt &count_id=it->second;
    ++(count_id.count);
    return;
  }

  // do not letify things with no children
  if(expr.operands().empty())
    return;

  Forall_operands(it, expr)
    collect_bindings(*it, map, let_order);

  INVARIANT(
    map.find(expr) == map.end(), "expression should not have been seen yet");

  symbol_exprt let=
    symbol_exprt("_let_"+std::to_string(++let_id_count), expr.type());

  map.insert(std::make_pair(expr, let_count_idt(1, let)));

  let_order.push_back(expr);
}

exprt smt2_convt::substitute_let(
  exprt &expr,
  const seen_expressionst &map)
{
  if(expr.operands().empty())
    return expr;

  let_visitort lv(map);

  Forall_operands(it, expr)
    it->visit(lv);

  return expr;
}
