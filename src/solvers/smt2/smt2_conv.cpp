/*******************************************************************\

Module: SMT Backend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/fixedbv.h>
#include <util/pointer_offset_size.h>
#include <util/ieee_float.h>
#include <util/base_type.h>
#include <util/string2int.h>

#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/flatten_byte_operators.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>

#include "smt2_conv.h"

// Mark different kinds of error condition
// General
#define UNREACHABLE throw "Supposidly unreachable location reached"
#define PARSERERROR(S) throw S

// Error checking the expression type
#define INVALIDEXPR(S) throw "Invalid expression: " S

// Unexpected types and other combination not implemented and not expected to be needed
#define UNEXPECTEDCASE(S) throw "Unexpected case: " S

// General todos
#define TODO(S) throw "TODO: " S

/*******************************************************************\

Function: smt2_convt::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::print_assignment(std::ostream &out) const
{
  // Boolean stuff
  
  for(std::size_t v=0; v<boolean_assignment.size(); v++)
    out << "b" << v << "=" << boolean_assignment[v] << "\n";

  // others
}

/*******************************************************************\

Function: smt2_convt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt smt2_convt::l_get(literalt l) const
{
  if(l.is_true()) return tvt(true);
  if(l.is_false()) return tvt(false);
  assert(l.var_no()<boolean_assignment.size());
  return tvt(boolean_assignment[l.var_no()]^l.sign());
}

/*******************************************************************\

Function: smt2_convt::write_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::write_header()
{
  out << "; SMT 2" << "\n";
  
  switch(solver)
  {
  case GENERIC: break;
  case BOOLECTOR: out << "; Generated for Boolector\n"; break;
  case CVC3: out << "; Generated for CVC 3\n"; break;
  case CVC4: out << "; Generated for CVC 4\n"; break;
  case MATHSAT: out << "; Generated for MathSAT\n"; break;
  case OPENSMT: out << "; Generated for OPENSMT\n"; break;
  case YICES: out << "; Generated for Yices\n"; break;
  case Z3: out << "; Generated for Z3\n"; break;
  }

  out << "(set-info :source \"" << notes << "\")" << "\n";
  
  out << "(set-option :produce-models true)" << "\n";

  // We use a broad mixture of logics, so on some solvers
  // its better not to declare here.
  // set-logic should come after setting options
  if(emit_set_logic && !logic.empty())
    out << "(set-logic " << logic << ")" << "\n";
}

/*******************************************************************\

Function: smt2_convt::write_footer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  for(defined_expressionst::iterator it = object_sizes.begin();
      it != object_sizes.end();
      ++it)
  {
    define_object_size(it->second, it->first);
  }
  
  out << "(check-sat)" << "\n";
  out << "\n";

  if (solver!=BOOLECTOR)
  {
    for(smt2_identifierst::const_iterator
        it=smt2_identifiers.begin();
        it!=smt2_identifiers.end();
        it++)
      out << "(get-value (|" << *it << "|))" << "\n";
  }

  out << "\n";

  out << "(exit)\n";
  
  out << "; end of SMT2 file" << "\n";
}

/*******************************************************************\

Function: smt2_convt::define_object_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::define_object_size(
  const irep_idt &id,
  const exprt &expr)
{
  assert(expr.id() == ID_object_size);
  const exprt &ptr = expr.op0();
  std::size_t size_width = boolbv_width(expr.type());
  std::size_t pointer_width = boolbv_width(ptr.type());
  unsigned int number = 0;
  unsigned int h = pointer_width - 1;
  unsigned int l = pointer_width - BV_ADDR_BITS;

  for(pointer_logict::objectst::const_iterator it = pointer_logic.objects.begin();
      it != pointer_logic.objects.end();
      ++it, number++)
  {
    const exprt &o = *it;
    const typet &type = ns.follow(o.type());
    exprt size_expr = size_of_expr(type, ns);
    mp_integer object_size;

    if (o.id() != ID_symbol)
      continue;

    if (size_expr.is_nil())
      continue;

    if (to_integer(size_expr, object_size))
      continue;

    out << "(assert (implies (= " <<
      "((_ extract " << h << " " << l << ") ";
    convert_expr(ptr);
    out << ") (_ bv" << number << " " << BV_ADDR_BITS << "))" <<
      "(= " << id << " (_ bv" << object_size.to_ulong() << " " <<
      size_width << "))))\n";
  }
}

/*******************************************************************\

Function: smt2_convt::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_convt::dec_solve()
{
  write_footer(out);
  return decision_proceduret::D_ERROR;
}

/*******************************************************************\

Function: smt2_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::get(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(expr).get_identifier();

    identifier_mapt::const_iterator it=identifier_map.find(id);

    if(it!=identifier_map.end())
      return it->second.value;
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    exprt tmp=get(member_expr.struct_op());
    if(tmp.is_nil()) return nil_exprt();
    return member_exprt(tmp, member_expr.get_component_name(), expr.type());
  }

  return nil_exprt();
}

/*******************************************************************\

Function: smt2_convt::parse_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  // * Decimal -- this is a decimal expansion of a real number and is of the form:
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
      PARSERERROR("smt2_convt::parse_literal can't parse \""+s+"\"");
  }
  else if(src.get_sub().size()==3 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id_string().substr(0, 2)=="bv") // (_ bvDECIMAL_VALUE SIZE)
  {
    value=string2integer(src.get_sub()[1].id_string().substr(2));
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="fp") // (fp signbv exponentbv significandbv)
  {
    if(type.id()==ID_floatbv)
    {
      const floatbv_typet &floatbv_type=to_floatbv_type(type);
      constant_exprt s1=parse_literal(src.get_sub()[1], bv_typet(1));
      constant_exprt s2=parse_literal(src.get_sub()[2], bv_typet(floatbv_type.get_e()));
      constant_exprt s3=parse_literal(src.get_sub()[3], bv_typet(floatbv_type.get_f()));
      // stitch the bits together
      std::string bits=id2string(s1.get_value())+
                       id2string(s2.get_value())+
                       id2string(s3.get_value());
      value=binary2integer(bits, 2);
    }
    else
      value=0;
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="+oo") // (_ +oo e s)
  {
    unsigned e=unsafe_string2unsigned(src.get_sub()[2].id_string());
    unsigned s=unsafe_string2unsigned(src.get_sub()[3].id_string());
    return ieee_floatt::plus_infinity(ieee_float_spect(s, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="-oo") // (_ -oo e s)
  {
    unsigned e=unsafe_string2unsigned(src.get_sub()[2].id_string());
    unsigned s=unsafe_string2unsigned(src.get_sub()[3].id_string());
    return ieee_floatt::minus_infinity(ieee_float_spect(s, e)).to_expr();
  }
  else if(src.get_sub().size()==4 &&
          src.get_sub()[0].id()=="_" &&
          src.get_sub()[1].id()=="NaN") // (_ NaN e s)
  {
    unsigned e=unsafe_string2unsigned(src.get_sub()[2].id_string());
    unsigned s=unsafe_string2unsigned(src.get_sub()[3].id_string());
    return ieee_floatt::NaN(ieee_float_spect(s, e)).to_expr();
  }
  
  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_bv ||
     type.id()==ID_c_enum ||
     type.id()==ID_c_bool)
  {
    return from_integer(value, type);
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return from_integer(value,
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
    UNEXPECTEDCASE("smt2_convt::parse_literal can't do type "+type.id_string());
}

/*******************************************************************\

Function: smt2_convt::parse_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::parse_array(
  const irept &src,
  const array_typet &type)
{
  if(src.get_sub().size()==4 && src.get_sub()[0].id()=="store")
  {
    // (store array index value)
    if(src.get_sub().size()!=4) return nil_exprt();
    
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

/*******************************************************************\

Function: smt2_convt::parse_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::parse_union(
  const irept &src,
  const union_typet &type)
{
  // these are always flat
  assert(!type.components().empty());
  const union_typet::componentt &first=type.components().front();
  std::size_t width=boolbv_width(type);
  exprt value=parse_rec(src, bv_typet(width));
  if(value.is_nil()) return nil_exprt();
  exprt converted=typecast_exprt(value, first.type());
  return union_exprt(first.get_name(), converted, type);
}

/*******************************************************************\

Function: smt2_convt::parse_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::parse_struct(
  const irept &src,
  const struct_typet &type)
{
  const struct_typet::componentst &components =
    type.components();

  struct_exprt result(type);

  result.operands().resize(components.size(), nil_exprt());
  
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
    exprt l=parse_literal(src, bv_typet(total_width));
    if(!l.is_constant()) return nil_exprt();
    
    irep_idt binary=to_constant_expr(l).get_value();
    if(binary.size()!=total_width) return nil_exprt();
    
    std::size_t offset=0;

    for(std::size_t i=0; i<components.size(); i++)
    {
      std::size_t component_width=boolbv_width(components[i].type());
      
      assert(offset+component_width<=total_width);
      std::string component_binary=
        "#b"+id2string(binary).substr(total_width-offset-component_width, component_width);
        
      result.operands()[i]=parse_rec(irept(component_binary), components[i].type());
    
      offset+=component_width;
    }
  }

  return result;
}

/*******************************************************************\

Function: smt2_convt::parse_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::parse_rec(const irept &src, const typet &_type)
{
  const typet &type=ns.follow(_type);
  
  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_bv ||
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
    constant_exprt bv_expr=parse_literal(src, bv_typet(width));

    mp_integer v;
    to_integer(bv_expr, v);

    // split into object and offset
    mp_integer pow=power(2, width-BV_ADDR_BITS);
    pointer_logict::pointert ptr;
    ptr.object=integer2long(v/pow);
    ptr.offset=v%pow;
    return pointer_logic.pointer_expr(ptr, type);
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

/*******************************************************************\

Function: smt2_convt::convert_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      << pointer_logic.add_object(expr) << " " << BV_ADDR_BITS << ")"
      << " (_ bv0 " << boolbv_width(result_type)-BV_ADDR_BITS << "))";
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      INVALIDEXPR("index takes two operands");

    const exprt &array=to_index_expr(expr).array();
    const exprt &index=to_index_expr(expr).index();

    if(index.is_zero())
    {
      if(array.type().id()==ID_pointer)
        convert_expr(array);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array, result_type);
      else
        assert(false);
    }
    else
    {
      // this is really pointer arithmetic
      exprt new_index_expr=expr;
      new_index_expr.op1()=gen_zero(index.type());

      exprt address_of_expr(ID_address_of, pointer_typet());
      address_of_expr.type().subtype()=array.type().subtype();
      address_of_expr.copy_to_operands(new_index_expr);

      exprt plus_expr(ID_plus, address_of_expr.type());
      plus_expr.copy_to_operands(address_of_expr, index);

      convert_expr(plus_expr);
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()!=1)
      INVALIDEXPR("member takes one operand");

    const member_exprt &member_expr=to_member_expr(expr);

    const exprt &struct_op=member_expr.struct_op();
    const typet &struct_op_type=ns.follow(struct_op.type());

    if(struct_op_type.id()==ID_struct)
    {
      const struct_typet &struct_type=
        to_struct_type(struct_op_type);

      const irep_idt &component_name=
        member_expr.get_component_name();

      mp_integer offset=member_offset(struct_type, component_name, ns);

      unsignedbv_typet index_type;
      index_type.set_width(boolbv_width(result_type));

      // pointer arithmetic
      out << "(bvadd ";
      convert_address_of_rec(struct_op, result_type);
      convert_expr(from_integer(offset, index_type));
      out << ")"; // bvadd
    }
    else
      UNEXPECTEDCASE("unexpected type of member operand");

  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    out << "(ite ";
    convert_expr(expr.op0());
    out << " ";
    convert_address_of_rec(expr.op1(), result_type);
    out << " ";
    convert_address_of_rec(expr.op2(), result_type);
    out << ")";
  }
  else
    UNEXPECTEDCASE("don't know how to take address of: "+expr.id_string());
}

/*******************************************************************\

Function: smt2_convt::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_byte_extract(const byte_extract_exprt &expr)
{
  // we just run the flattener
  exprt flattened_expr=flatten_byte_extract(expr, ns);
  unflatten(BEGIN, expr.type());
  convert_expr(flattened_expr);
  unflatten(END, expr.type());
}

/*******************************************************************\

Function: smt2_convt::convert_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_byte_update(const byte_update_exprt &expr)
{
  assert(expr.operands().size()==3);

  // The situation: expr.op0 needs to be split in 3 parts
  // |<--- L --->|<--- M --->|<--- R --->|
  // where M is the expr.op1'th byte
  // We need to output L expr.op2 R

  mp_integer i;
  if(to_integer(expr.op1(), i))
    INVALIDEXPR("byte_extract takes constant as second parameter");

  std::size_t total_width=boolbv_width(expr.op().type());
  std::size_t value_width=boolbv_width(expr.value().type());

  if(total_width==0)
    INVALIDEXPR("failed to get width of byte_update");

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
    if(lower==0) // the update expression is expr.op2()
    {
      flatten2bv(expr.op2());
    }
    else // uppermost byte selected, only R needed
    {
      out << "(concat ";
      flatten2bv(expr.op2());
      out << " ((_ extract " << lower-1 << " 0) ";
      flatten2bv(expr.op0());
      out << "))";
    }
  }
  else
  {
    if(lower==0) // lowermost byte selected, only L needed
    {
      out << "(concat ";
      out << "((_ extract " << max << " " << (upper+1) << ") ";
      flatten2bv(expr.op0());
      out << ") ";
      flatten2bv(expr.op2());
      out << ")";
    }
    else // byte in the middle selected, L & R needed
    {
      out << "(concat (concat ";
      out << "((_ extract " << max << " " << (upper+1) << ") ";
      flatten2bv(expr.op0());
      out << ") ";
      flatten2bv(expr.op2());
      out << ") ((_ extract " << (lower-1) << " 0) ";
      flatten2bv(expr.op0());
      out << "))";
    }
  }

  unflatten(END, expr.type());    
}

/*******************************************************************\

Function: smt2_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt2_convt::convert(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

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

/*******************************************************************\

Function: smt2_convt::convert_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

    smt2_identifiers.insert("B"+i2string(l.var_no()));
  }
}

/*******************************************************************\

Function: smt2_convt::convert_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      result+=i2string(ch);
      result+=';';
      break;
      
    case '$': // $ _is_ allowed
    default:
      result+=ch;
    }
  }
  
  return result;
}

/*******************************************************************\

Function: smt2_convt::type2id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_convt::type2id(const typet &type)
{
  if(type.id()==ID_floatbv)
  {
    ieee_float_spect spec(to_floatbv_type(type));
    return "f"+i2string(spec.width())+"_"+i2string(spec.f);
  }
  else if(type.id()==ID_unsignedbv)
  {
    return "u"+i2string(to_unsignedbv_type(type).get_width());
  }
  else if(type.id()==ID_c_bool)
  {
    return "u"+i2string(to_c_bool_type(type).get_width());
  }
  else if(type.id()==ID_signedbv)
  {
    return "s"+i2string(to_signedbv_type(type).get_width());
  }
  else if(type.id()==ID_bool)
  {
    return "b";
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return type2id(type.subtype());
  }
  else
  {
    assert(false);
    return "";
  }
}

/*******************************************************************\

Function: smt2_convt::floatbv_suffix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_convt::floatbv_suffix(const exprt &expr)
{
  assert(!expr.operands().empty());
  return "_"+type2id(expr.op0().type())+"->"+type2id(expr.type());
}

/*******************************************************************\

Function: smt2_convt::convert_floatbv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv(const exprt &expr)
{
  assert(!use_FPA_theory);

  if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    out << '|' << convert_identifier(id) << '|';
    return;
  }

  if(expr.id()==ID_smt2_symbol)
  {
    irep_idt id=to_smt2_symbol(expr).get_identifier();
    out << id;
    return;
  }

  assert(!expr.operands().empty());

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

/*******************************************************************\

Function: smt2_convt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_expr(const exprt &expr)
{
  // huge monster case split over expression id
  if(expr.id()==ID_symbol)
  {
    irep_idt id=to_symbol_expr(expr).get_identifier();
    assert(id!=irep_idt());

    out << '|' << convert_identifier(id) << '|';
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    assert(id!="");
    out << '|' << convert_identifier("nondet_"+id2string(id)) << '|';
  }
  else if(expr.id()==ID_smt2_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    assert(id!=irep_idt());
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
    assert(expr.operands().size()>=2);

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
    assert(expr.operands().size()==1);
    
    if(expr.type().id()==ID_vector)
    {
      if(use_datatypes)
      {
        assert(datatype_map.find(expr.type()) != datatype_map.end());

        const std::string smt_typename=
          datatype_map.find(expr.type())->second;

        // extract elements
        const vector_typet &vector_type=to_vector_type(expr.type());
        
        mp_integer size;
        if(to_integer(vector_type.size(), size))
          INVALIDEXPR("failed to convert vector size to constant");

        out << "(let ((?vectorop ";
        convert_expr(expr.op0());
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
        TODO("bitnot for vectors");
    }
    else
    {
      out << "(bvnot ";
      convert_expr(expr.op0());
      out << ")";
    }
  }
  else if(expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);

    if(expr.type().id()==ID_rational)
    {
      out << "(- ";
      convert_expr(expr.op0());
      out << ")";
    }
    else if(expr.type().id()==ID_floatbv)
    {
      // this has no rounding mode
      if(use_FPA_theory)
      {
        out << "(fp.neg ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else if(expr.type().id()==ID_vector)
    {
      if(use_datatypes)
      {
        assert(datatype_map.find(expr.type()) != datatype_map.end());

        const std::string smt_typename=
          datatype_map.find(expr.type())->second;

        // extract elements
        const vector_typet &vector_type=to_vector_type(expr.type());
        
        mp_integer size;
        if(to_integer(vector_type.size(), size))
          INVALIDEXPR("failed to convert vector size to constant");

        out << "(let ((?vectorop ";
        convert_expr(expr.op0());
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
        TODO("unary minus for vector");
    }
    else
    {
      out << "(bvneg ";
      convert_expr(expr.op0());
      out << ")";
    }
  }
  else if(expr.id()==ID_unary_plus)
  {
    // A no-op (apart from type promotion)
    assert(expr.operands().size()==1);
    convert_expr(expr.op0());
  }
  else if(expr.id()==ID_sign)
  {
    assert(expr.operands().size() == 1);
    
    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
	out << "(fp.isNegative ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else if(op_type.id()==ID_signedbv)
    {
      std::size_t op_width=to_signedbv_type(op_type).get_width();
            
      out << "(bvslt ";
      convert_expr(expr.op0());
      out << " (_ bv0 " << op_width << "))";
    }
    else
      UNEXPECTEDCASE("sign applied to type " + expr.type().id_string());
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);

    out << "(ite ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << " ";
    convert_expr(expr.op2());
    out << ")";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);

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
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==2);

    out << "(=> ";
    convert_expr(expr.op0());
    out << " ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==1);

    out << "(not ";
    convert_expr(expr.op0());
    out << ")";
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));

    if(expr.id()==ID_notequal)
    {
      out << "(not (= ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << "))";
    }
    else
    {
      out << "(= ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    // These are not the same as (= A B)
    // because of NaN and negative zero.
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));

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
    assert(expr.operands().size()==1);
    assert(expr.type().id()==ID_pointer);
    convert_address_of_rec(expr.op0(), to_pointer_type(expr.type()));
  }
  else if(expr.id()==ID_array_of)
  {
    assert(expr.type().id()==ID_array);
    assert(expr.operands().size()==1);
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    assert(it!=defined_expressions.end());
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
    const typet &type=expr.type();

    assert(expr.operands().size()==2);

    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv)
    {
      if(expr.id()==ID_ashr)
        out << "(bvashr ";
      else if(expr.id()==ID_lshr)
        out << "(bvlshr ";
      else if(expr.id()==ID_shl)
        out << "(bvshl ";
      else
        assert(false);

      convert_expr(expr.op0());
      out << " ";

      // SMT2 requires the shift distance to have the same width as
      // the value that is shifted -- odd!
      
      if(expr.op1().type().id()==ID_integer)
      {
        mp_integer i;
        if(to_integer(expr.op1(), i))
          UNEXPECTEDCASE("op1 on shift not a constant");

        // shift distance must be bit vector
        std::size_t width_op0=boolbv_width(expr.op0().type());
        exprt tmp=from_integer(i, unsignedbv_typet(width_op0));
        convert_expr(tmp);
      }
      else if(expr.op1().type().id()==ID_signedbv ||
              expr.op1().type().id()==ID_unsignedbv ||
              expr.op1().type().id()==ID_c_enum ||
              expr.op1().type().id()==ID_c_bool)
      {
        std::size_t width_op0=boolbv_width(expr.op0().type());
        std::size_t width_op1=boolbv_width(expr.op1().type());

        if(width_op0==width_op1)
          convert_expr(expr.op1());
        else if(width_op0>width_op1)
        {
          out << "((_ zero_extend " << width_op0-width_op1 << ") ";
          convert_expr(expr.op1());
          out << ")"; // zero_extend
        }
        else // width_op0<width_op1
        {
          out << "((_ extract " << width_op0-1 << " 0) ";
          convert_expr(expr.op1());
          out << ")"; // extract
        }
      }
      else
        UNEXPECTEDCASE("unsupported op1 type for "+expr.id_string()+": "+type.id_string());
      
      out << ")"; // bv*sh
    }
    else
      UNEXPECTEDCASE("unsupported type for "+expr.id_string()+": "+type.id_string());
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
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    std::size_t offset_bits=boolbv_width(expr.op0().type())-BV_ADDR_BITS;
    std::size_t result_width=boolbv_width(expr.type());

    // max extract width    
    if(offset_bits>result_width) offset_bits=result_width;
    
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
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()==ID_pointer);
    std::size_t ext=boolbv_width(expr.type())-BV_ADDR_BITS;
    std::size_t pointer_width=boolbv_width(expr.op0().type());

    if(ext>0)
      out << "((_ zero_extend " << ext << ") ";

    out << "((_ extract "
        << pointer_width-1 << " "
        << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    out << ")";

    if(ext>0)
      out << ")"; // zero_extend
  }
  else if(expr.id()==ID_dynamic_object)
  {
    convert_is_dynamic_object(expr);
  }
  else if(expr.id()=="invalid-pointer")
  {
    assert(expr.operands().size()==1);

    std::size_t pointer_width=boolbv_width(expr.op0().type());
    out << "(= ((_ extract "
        << pointer_width-1 << " "
        << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    out << ") (_ bv" << pointer_logic.get_invalid_object()
        << " " << BV_ADDR_BITS << "))";
  }
  else if(expr.id()=="pointer_object_has_type")
  {
    assert(expr.operands().size()==1);

    out << "false"; // TODO
    TODO("pointer_object_has_type not implemented");
  }
  else if(expr.id()==ID_string_constant)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    assert(it!=defined_expressions.end());
    out << it->second;
  }
  else if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op1().is_constant())
    {
      mp_integer i;
      if(to_integer(expr.op1(), i))
        INVALIDEXPR("extractbit: to_integer failed");

      out << "(= ((_ extract " << i << " " << i << ") ";
      flatten2bv(expr.op0());
      out << ") #b1)";
    }
    else
    {
      out << "(= ((_ extract 0 0) ";
      // the arguments of the shift need to have the same width
      out << "(bvlshr ";
      flatten2bv(expr.op0());
      typecast_exprt tmp(expr.op0().type());
      tmp.op0()=expr.op1();
      convert_expr(tmp);
      out << ")) bin1)"; // bvlshr, extract, =
    }
  }
  else if(expr.id()==ID_extractbits)
  {
    assert(expr.operands().size()==3);
    
    if(expr.op1().is_constant() &&
       expr.op2().is_constant())
    {
      mp_integer op1_i, op2_i;
      if(to_integer(expr.op1(), op1_i))
        INVALIDEXPR("extractbits: to_integer failed");

      if(to_integer(expr.op2(), op2_i))
        INVALIDEXPR("extractbits: to_integer failed");

      if(op2_i>op1_i) std::swap(op1_i, op2_i);
      
      // now op1_i>=op2_i

      out << "((_ extract " << op1_i << " " << op2_i << ") ";
      flatten2bv(expr.op0());
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
      TODO("smt2: extractbits with non-constant index");
    }
  }
  else if(expr.id()==ID_replication)
  {
    assert(expr.operands().size()==2);

    mp_integer times;
    if(to_integer(expr.op0(), times))
      INVALIDEXPR("replication takes constant as first parameter");

    out << "((_ repeat " << times << ") ";
    flatten2bv(expr.op1());
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
    boolbv_widtht boolbv_width(ns);
  
    std::size_t result_width=boolbv_width(expr.type());
    
    if(result_width==0)
      INVALIDEXPR("conversion failed");

    if(expr.operands().size()!=1)
      INVALIDEXPR("width expects 1 operand");

    std::size_t op_width=boolbv_width(expr.op0().type());
    
    if(op_width==0)
      INVALIDEXPR("conversion failed");

    out << "(_ bv" << op_width/8
        << " " << result_width << ")";
  }
  else if(expr.id()==ID_abs)
  {
    assert(expr.operands().size()==1);

    const typet &type=expr.type();

    if(type.id()==ID_signedbv)
    {
      std::size_t result_width = to_signedbv_type(type).get_width();
            
      out << "(ite (bvslt ";
      convert_expr(expr.op0());
      out << " (_ bv0 " << result_width << ")) ";
      out << "(bvneg ";
      convert_expr(expr.op0());
      out << ") ";
      convert_expr(expr.op0());
      out << ")";
    }
    else if(type.id()==ID_fixedbv)
    {
      std::size_t result_width=to_fixedbv_type(type).get_width();
      
      out << "(ite (bvslt ";
      convert_expr(expr.op0());
      out << " (_ bv0 " << result_width << ")) ";
      out << "(bvneg ";
      convert_expr(expr.op0());
      out << ") ";
      convert_expr(expr.op0());
      out << ")";
    }
    else if(type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
	out << "(fp.abs ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else
      UNEXPECTEDCASE("abs with unsupported operand type");
  }
  else if(expr.id()==ID_isnan)
  {
    assert(expr.operands().size()==1);

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
      out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isNaN ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else
      UNEXPECTEDCASE("isnan with unsupported operand type");
  }
  else if(expr.id()==ID_isfinite)
  {
    if(expr.operands().size()!=1)
      INVALIDEXPR("isfinite expects one operand");

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
      out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
	out << "(and ";

	out << "(not (fp.isNaN ";
        convert_expr(expr.op0());
        out << "))";

	out << "(not (fp.isInf ";
        convert_expr(expr.op0());
        out << "))";

	out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else
      UNEXPECTEDCASE("isfinite with unsupported operand type");
  }
  else if(expr.id()==ID_isinf)
  {
    if(expr.operands().size()!=1)
      INVALIDEXPR("isinf expects one operand");

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
      out << "false";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
	out << "(fp.isInfinite ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else
      UNEXPECTEDCASE("isinf with unsupported operand type");
  }
  else if(expr.id()==ID_isnormal)
  {
    if(expr.operands().size()!=1)
      INVALIDEXPR("isnormal expects one operand");

    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_fixedbv)
      out << "true";
    else if(op_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        out << "(fp.isNormal ";
        convert_expr(expr.op0());
        out << ")";
      }
      else
        convert_floatbv(expr);
    }
    else
      UNEXPECTEDCASE("isnormal with unsupported operand type");
  }
  else if(expr.id()==ID_overflow_plus ||
          expr.id()==ID_overflow_minus)
  {
    assert(expr.operands().size()==2);
    assert(expr.type().id()==ID_bool);

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
      UNEXPECTEDCASE("overflow check on unknown type: "+op_type.id_string());
  }
  else if(expr.id()==ID_overflow_mult)
  {
    assert(expr.operands().size()==2);

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
      out << "(or (bvsge prod (_ bv" << power(2, width-1) << " " << width*2 << "))";
      out << " (bvslt prod (bvneg (_ bv" << power(2, width-1) << " " << width*2 << ")))))";
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
      UNEXPECTEDCASE("overflow-* check on unknown type: "+op_type.id_string());
  }
  else if(expr.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    assert(it!=defined_expressions.end());
    out << it->second;
  }
  else if(expr.id()==ID_literal)
  {
    convert_literal(to_literal_expr(expr).get_literal());
  }
  else if(expr.id()==ID_forall || 
          expr.id()==ID_exists)
  {
    if(expr.id()==ID_forall)
      out << "(forall ";
    else if(expr.id()==ID_exists)
      out << "(exists ";

    exprt bound=expr.op0();

    out << "((";
    convert_expr(bound);
    out << " ";
    convert_type(bound.type());
    out << ")) ";

    convert_expr(expr.op1());

    out << ")";
  }
  else if(expr.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(expr.type());
   
    mp_integer size;
    if(to_integer(vector_type.size(), size))
      INVALIDEXPR("failed to convert vector size to constant");
      
    assert(size==expr.operands().size());
      
    if(use_datatypes)
    {
      assert(datatype_map.find(vector_type)!=datatype_map.end());

      const std::string smt_typename=
        datatype_map.find(vector_type)->second;
      
      out << "(mk-" << smt_typename;
    }
    else
      out << "(concat";
      
    // build component-by-component
    forall_operands(it, expr)
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
  else
    UNEXPECTEDCASE("smt2_convt::convert_expr: `"+expr.id_string()+"' is unsupported");
}

/*******************************************************************\

Function: smt2_convt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_typecast(const typecast_exprt &expr)
{
  assert(expr.operands().size()==1);
  const exprt &src=expr.op0();

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
       src_type.id()==ID_pointer)
    {
      out << "(not (= ";
      convert_expr(src);
      out << " ";
      convert_expr(gen_zero(src_type));
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
    convert_expr(gen_zero(src_type));
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
      out << " (= ((_ extract " << (from_width-1) << " " << (from_width-1) << ") ?tcop) "
             "#b1)";
      
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
          TODO("bit-wise floatbv to bv");
        }
        else
        {
          // straight-forward if width matches
          convert_expr(src);
        }
      }
      else if (dest_type.id()==ID_signedbv)
      {
        // this should be floatbv_typecast, not typecast
        UNEXPECTEDCASE("typecast unexpected "+src_type.id_string()+" -> "+dest_type.id_string());
      }
      else if (dest_type.id()==ID_unsignedbv)
      {
        // this should be floatbv_typecast, not typecast
        UNEXPECTEDCASE("typecast unexpected "+src_type.id_string()+" -> "+dest_type.id_string());
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
        mp_integer i;
        to_integer(src, i);
        out << "(_ bv" << i << " " << to_width << ")";
      }
      else
        TODO("can't convert non-constant integer to bitvector");
    }
    else if(src_type.id()==ID_struct) // flatten a struct to a bit-vector
    {
      if(use_datatypes)
      {
        assert(boolbv_width(src_type)==boolbv_width(dest_type));
        flatten2bv(src);
      }
      else
      {
        assert(boolbv_width(src_type)==boolbv_width(dest_type));
        convert_expr(src); // nothing else to do!
      }
    }
    else if(src_type.id()==ID_union) // flatten a union
    {
      assert(boolbv_width(src_type)==boolbv_width(dest_type));
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
      UNEXPECTEDCASE("TODO typecast2 "+src_type.id_string()+" -> "+dest_type.id_string() + " src == " + from_expr(ns, "", src));
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
        assert(from_width<to_integer_bits);
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
        assert(to_integer_bits>from_integer_bits);
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
        assert(to_fraction_bits>from_fraction_bits);
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
    TODO("range typecast");
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
      constant_exprt val(dest_type);

      ieee_floatt a;
      a.spec=to_floatbv_type(dest_type);

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
      exprt tmp=typecast_exprt(src, bool_typet());
      convert_typecast(typecast_exprt(tmp, dest_type));
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> float");
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
    UNEXPECTEDCASE("TODO typecast8 "+src_type.id_string()+" -> "+dest_type.id_string());
}

/*******************************************************************\

Function: smt2_convt::convert_floatbv_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  const exprt &src=expr.op();
  //const exprt &rounding_mode=expr.rounding_mode();
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
      tmp.op()=typecast_exprt(src, src_type.subtype());
      convert_floatbv_typecast(tmp);
    }
    else
      UNEXPECTEDCASE("TODO typecast11 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  else if(dest_type.id()==ID_signedbv)
  {
    if(use_FPA_theory)
    {
      unsigned dest_width=to_signedbv_type(dest_type).get_width();
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
      unsigned dest_width=to_unsignedbv_type(dest_type).get_width();
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
    UNEXPECTEDCASE("TODO typecast12 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
}

/*******************************************************************\

Function: smt2_convt::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_struct(const struct_exprt &expr)
{
  const struct_typet &struct_type=to_struct_type(expr.type());

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()==expr.operands().size());

  assert(!components.empty());
  
  if(use_datatypes)
  {
    assert(datatype_map.find(struct_type) != datatype_map.end());
    const std::string smt_typename =
      datatype_map.find(struct_type)->second;

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

/*******************************************************************\

Function: smt2_convt::flatten_array

  Inputs:

 Outputs:

 Purpose: produce a flat bit-vector for a given array of fixed size

\*******************************************************************/

void smt2_convt::flatten_array(const exprt &expr)
{
  const array_typet &array_type=
    to_array_type(ns.follow(expr.type()));

  mp_integer size;
  if(to_integer(array_type.size(), size))
    INVALIDEXPR("failed to convert array size for flattening");
    
  if(size==0)
    INVALIDEXPR("can't convert zero-sized array");
    
  out << "(let ((?far ";
  convert_expr(expr);
  out << ")) ";

  for(mp_integer i=size; i!=0; --i)
  {
    if(i!=1) out << "(concat ";
    out << "(select ?far ";
    convert_expr(from_integer(i-1, array_type.size().type()));
    out << ")";
    if(i!=1) out << " ";
  }
  
  // close the many parentheses
  for(mp_integer i=size; i>1; --i)
    out << ")";
  
  out << ")"; // let
}

/*******************************************************************\

Function: smt2_convt::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_union(const union_exprt &expr)
{
  const union_typet &union_type=to_union_type(expr.type());
  const exprt &op=expr.op();

  boolbv_widtht boolbv_width(ns);

  std::size_t total_width=boolbv_width(union_type);

  if(total_width==0)
    INVALIDEXPR("failed to get union width for union");

  std::size_t member_width=boolbv_width(op.type());

  if(member_width==0)
    INVALIDEXPR("failed to get union member width for union");

  if(total_width==member_width)
  {
    flatten2bv(op);
  }
  else
  {
    // we will pad with zeros, but non-det would be better
    assert(total_width>member_width);
    out << "(concat ";
    out << "(_ bv0 "
        << (total_width-member_width) << ") ";
    flatten2bv(op);
    out << ")";
  }
}

/*******************************************************************\

Function: smt2_convt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    mp_integer value=binary2integer(id2string(expr.get_value()), false);

    std::size_t width=boolbv_width(expr_type);

    out << "(_ bv" << value
        << " " << width << ")";
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr_type));

    std::string v_str=id2string(expr.get_value());
    mp_integer v=binary2integer(v_str, false);

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
      size_t e = floatbv_type.get_e();
      size_t f = floatbv_type.get_f() + 1;

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
	if (v.get_sign())
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
      UNEXPECTEDCASE("unknown boolean constant");
  }
  else if(expr_type.id()==ID_array)
  {
    defined_expressionst::const_iterator it=defined_expressions.find(expr);
    assert(it!=defined_expressions.end());
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
      out << "(/ " << value.substr(0,pos) << ".0 "
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

/*******************************************************************\

Function: smt2_convt::convert_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_mod(const mod_exprt &expr)
{
  assert(expr.operands().size()==2);

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

/*******************************************************************\

Function: smt2_convt::convert_is_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_is_dynamic_object(const exprt &expr)
{
  std::vector<unsigned> dynamic_objects;
  pointer_logic.get_dynamic_objects(dynamic_objects);

  assert(expr.operands().size()==1);

  if(dynamic_objects.empty())
    out << "false";
  else
  {
    std::size_t pointer_width=boolbv_width(expr.op0().type());
  
    out << "(let ((?obj ((_ extract " 
        << pointer_width-1 << " "
        << pointer_width-BV_ADDR_BITS << ") ";
    convert_expr(expr.op0());
    out << "))) ";

    if(dynamic_objects.size()==1)
    {
      out << "(= (_ bv" << dynamic_objects.front()
          << " " << BV_ADDR_BITS << ") ?obj)";
    }
    else
    {
      out << "(or";

      for(std::vector<unsigned>::const_iterator
          it=dynamic_objects.begin();
          it!=dynamic_objects.end();
          it++)
        out << " (= (_ bv" << *it
            << " " << BV_ADDR_BITS << ") ?obj)";

      out << ")"; // or
    }

    out << ")"; // let
  }
}

/*******************************************************************\

Function: smt2_convt::convert_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_relation(const exprt &expr)
{
  assert(expr.operands().size()==2);

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
    UNEXPECTEDCASE("unsupported type for "+expr.id_string()+": "+op_type.id_string());

}

/*******************************************************************\

Function: smt2_convt::convert_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_plus(const plus_exprt &expr)
{
  if(expr.operands().size()==0)
  {
    INVALIDEXPR("No operands to plus");
  }
  else if(expr.operands().size()==1)
  {
    convert_expr(expr.op0());
  }
  else if(expr.operands().size()==2)
  {
    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_fixedbv)
    {
      // These could be chained, i.e., need not be binary,
      // but at least MathSat doesn't like that.
      out << "(bvadd ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
    else if(expr.type().id()==ID_floatbv)
    {
      // Floating-point additions should have be been converted
      // to ID_floatbv_plus during symbolic execution, adding 
      // the rounding mode.  See smt2_convt::convert_floatbv_plus.
      UNREACHABLE;
    }
    else if(expr.type().id()==ID_pointer)
    {
      exprt p=expr.op0(), i=expr.op1();

      if(p.type().id()!=ID_pointer)
        p.swap(i);

      if(p.type().id()!=ID_pointer)
        INVALIDEXPR("unexpected mixture in pointer arithmetic");

      mp_integer element_size=
        pointer_offset_size(expr.type().subtype(), ns);

      out << "(bvadd ";
      convert_expr(p);
      out << " ";

      if(element_size>=2)
      {
        out << "(bvmul ";
        convert_expr(i);
        out << " (_ bv" << element_size
                      << " " << boolbv_width(expr.type()) << "))";
      }
      else
        convert_expr(i);

      out << ")";
    }
    else if(expr.type().id()==ID_rational)
    {
      out << "(+";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
    else if(expr.type().id()==ID_vector)
    {
      const vector_typet &vector_type=to_vector_type(expr.type());
     
      mp_integer size;
      if(to_integer(vector_type.size(), size))
        INVALIDEXPR("failed to convert vector size to constant");
        
      typet index_type=vector_type.size().type();

      if(use_datatypes)
      {
        assert(datatype_map.find(vector_type)!=datatype_map.end());

        const std::string smt_typename=
          datatype_map.find(vector_type)->second;
        
        out << "(mk-" << smt_typename;
      }
      else
        out << "(concat";
        
      // add component-by-component
      for(mp_integer i=0; i!=size; ++i)
      {
        exprt tmp(ID_plus, vector_type.subtype());
        forall_operands(it, expr)
          tmp.copy_to_operands(
            index_exprt(*it, from_integer(size-i-1, index_type), vector_type.subtype()));

        out << " ";
        convert_expr(tmp);
      }

      out << ")"; // mk-... or concat
    }
    else
      UNEXPECTEDCASE("unsupported type for +: "+expr.type().id_string());
  }
  else
  {
    convert_plus(to_plus_expr(make_binary(expr)));
  }
}

/*******************************************************************\

Function: smt2_convt::convert_rounding_mode_FPA

  Inputs: The expression representing the rounding mode.

 Outputs: SMT-LIB output to out.

 Purpose: Converting a constant or symbolic rounding mode to SMT-LIB.
          Only called when use_FPA_theory is enabled

\*******************************************************************/

void smt2_convt::convert_rounding_mode_FPA(const exprt &expr)
{
  assert(use_FPA_theory);

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
      INVALIDEXPR("Unknown constant rounding mode with value "+id2string(cexpr.get_value()));
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

/*******************************************************************\

Function: smt2_convt::convert_floatbv_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv_plus(const ieee_float_op_exprt &expr)
{
  const typet &type=expr.type();

  assert(expr.operands().size()==3);
  assert(type.id()==ID_floatbv ||
         (type.id()==ID_complex && type.subtype().id()==ID_floatbv) ||
         (type.id()==ID_vector && type.subtype().id()==ID_floatbv));

  if(use_FPA_theory)
  {
    if(type.id()==ID_floatbv)
    {
      out << "(fp.add ";
      convert_rounding_mode_FPA(expr.op2());
      out << " ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";
    }
    else if(type.id()==ID_complex)
    {
      TODO("+ for floatbv complex");
    }
    else if(type.id()==ID_vector)
    {
      TODO("+ for floatbv vector");
    }
    else
      UNEXPECTEDCASE("unsupported type for +: "+type.id_string());
  }
  else
    convert_floatbv(expr);
}

/*******************************************************************\

Function: smt2_convt::convert_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_minus(const minus_exprt &expr)
{
  assert(expr.operands().size()==2);

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
    if(expr.op0().type().id()==ID_pointer &&
       expr.op1().type().id()==ID_pointer)
    {
      // Pointer difference. 
      mp_integer element_size=
        pointer_offset_size(expr.op0().type().subtype(), ns);

      if(element_size>=2)
        out << "(bvsdiv ";

      assert(boolbv_width(expr.op0().type())==boolbv_width(expr.type()));
      
      out << "(bvsub ";
      convert_expr(expr.op0());
      out << " ";
      convert_expr(expr.op1());
      out << ")";

      if(element_size>=2)
        out << " (_ bv" << element_size
            << " " << boolbv_width(expr.type()) << "))";
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
    TODO("pointer subtraction");
  }
  else if(expr.type().id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(expr.type());
   
    mp_integer size;
    if(to_integer(vector_type.size(), size))
      INVALIDEXPR("failed to convert vector size to constant");
      
    typet index_type=vector_type.size().type();

    if(use_datatypes)
    {
      assert(datatype_map.find(vector_type)!=datatype_map.end());

      const std::string smt_typename=
        datatype_map.find(vector_type)->second;
      
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
          index_exprt(*it, from_integer(size-i-1, index_type), vector_type.subtype()));

      out << " ";
      convert_expr(tmp);
    }

    out << ")"; // mk-... or concat
  }
  else
    UNEXPECTEDCASE("unsupported type for -: "+expr.type().id_string());
}

/*******************************************************************\

Function: smt2_convt::convert_floatbv_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv_minus(const ieee_float_op_exprt &expr)
{
  assert(expr.operands().size()==3);
  assert(expr.type().id()==ID_floatbv);

  if(use_FPA_theory)
  {
    out << "(fp.sub ";
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

/*******************************************************************\

Function: smt2_convt::convert_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_div(const div_exprt &expr)
{
  assert(expr.operands().size()==2);

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
    unsigned fraction_bits=spec.get_fraction_bits();

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

/*******************************************************************\

Function: smt2_convt::convert_floatbv_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv_div(const ieee_float_op_exprt &expr)
{
  assert(expr.operands().size()==3);
  assert(expr.type().id()==ID_floatbv);

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

/*******************************************************************\

Function: smt2_convt::convert_mult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_mult(const mult_exprt &expr)
{
  assert(expr.operands().size()>=2);
  
  // re-write to binary if needed
  if(expr.operands().size()>2)
  {
    // strip last operand
    exprt tmp=expr;
    tmp.operands().pop_back();
  
    // recursive call
    return convert_mult(mult_exprt(tmp, expr.operands().back()));
  }
  
  assert(expr.operands().size()==2);

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
    unsigned fraction_bits=spec.get_fraction_bits();

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
  else if(expr.type().id()==ID_rational)
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

/*******************************************************************\

Function: smt2_convt::convert_floatbv_mult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_floatbv_mult(const ieee_float_op_exprt &expr)
{
  assert(expr.operands().size()==3);
  assert(expr.type().id()==ID_floatbv);
  
  if(use_FPA_theory)
  {
    out << "(fp.mul ";
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

/*******************************************************************\

Function: smt2_convt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_with(const with_exprt &expr)
{
  // get rid of "with" that has more than three operands
  
  assert(expr.operands().size()>=3);
  
  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();
  
    // strip of the trailing two operands
    exprt tmp=expr;
    tmp.operands().resize(s-2);
  
    with_exprt new_with_expr;
    assert(new_with_expr.operands().size()==3);
    new_with_expr.type()=expr.type();
    new_with_expr.old()=tmp;
    new_with_expr.where()=expr.operands()[s-2];
    new_with_expr.new_value()=expr.operands()[s-1];
    
    // recursive call  
    return convert_with(new_with_expr);
  }
  
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
      out << "(bvlshr (_ bv" << power(2, array_width)-1 << " " << array_width << ") ";
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

    if(!struct_type.has_component(component_name))
      INVALIDEXPR("with failed to find component in struct");

    if(use_datatypes)
    {
      assert(datatype_map.find(expr_type) != datatype_map.end());
      const std::string smt_typename=
        datatype_map.find(expr_type)->second;

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
            << "((_ extract " << (struct_width-1) << " " << m.width << ") ?withop) ";
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
            << "((_ extract " << (struct_width-1) << " " << (m.offset+m.width) << ") ?withop) ";
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

    if(total_width==0)
      INVALIDEXPR("failed to get union width for with");

    std::size_t member_width=boolbv_width(value.type());

    if(member_width==0)
      INVALIDEXPR("failed to get union member width for with");

    if(total_width==member_width)
    {
      flatten2bv(value);
    }
    else
    {
      assert(total_width>member_width);
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
    
    if(total_width==0)
      INVALIDEXPR("failed to get total width");

    assert(expr.operands().size()==3);
    const exprt &index=expr.operands()[1];
    const exprt &value=expr.operands()[2];

    std::size_t value_width=boolbv_width(value.type());

    if(value_width==0)
      INVALIDEXPR("failed to get value width");

    typecast_exprt index_tc(index, expr_type);

    // TODO: SMT2-ify
    TODO("SMT2-ify");
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
  }
  else
    UNEXPECTEDCASE("with expects struct, union, or array type, but got "+expr.type().id_string());
}

/*******************************************************************\

Function: smt2_convt::convert_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_update(const exprt &expr)
{
  assert(expr.operands().size()==3);

  TODO("smt2_convt::convert_update to be implemented");  
}

/*******************************************************************\

Function: smt2_convt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_index(const index_exprt &expr)
{
  assert(expr.operands().size()==2);
  
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
      assert(array_width!=0);

      unflatten(BEGIN, array_type.subtype());
      
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
      
      unflatten(END, array_type.subtype());
    }
  }
  else if(array_op_type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(array_op_type);
    
    if(use_datatypes)
    {
      assert(datatype_map.find(vector_type)!=datatype_map.end());
      const std::string smt_typename=
        datatype_map.find(vector_type)->second;
        
      // this is easy for constant indicies
      
      mp_integer index_int;
      if(to_integer(expr.index(), index_int))
      {
        TODO("non-constant index on vectors");
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
      TODO("index on vectors");
    }
  }
  else
    UNEXPECTEDCASE("index with unsupported array type: "+array_op_type.id_string());
}

/*******************************************************************\

Function: smt2_convt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_member(const member_exprt &expr)
{
  assert(expr.operands().size()==1);

  const member_exprt &member_expr=to_member_expr(expr);
  const exprt &struct_op=member_expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());
  const irep_idt &name=member_expr.get_component_name();

  if(struct_op_type.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(struct_op_type);

    if(!struct_type.has_component(name))
      INVALIDEXPR("failed to find struct member");

    if(use_datatypes)
    {
      assert(datatype_map.find(struct_type) != datatype_map.end());
      const std::string smt_typename=
        datatype_map.find(struct_type)->second;

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
      mp_integer member_offset=::member_offset(struct_type, name, ns);
      if(member_offset==-1)
        INVALIDEXPR("failed to get struct member offset");
        
      out << "((_ extract " << (member_offset*8+member_width-1)
          << " " << member_offset*8 << ") ";
      convert_expr(struct_op);
      out << ")";
    }
  }
  else if(struct_op_type.id()==ID_union)
  {
    std::size_t width=boolbv_width(expr.type());
      
    if(width==0)
      INVALIDEXPR("failed to get union member width");

    unflatten(BEGIN, expr.type());

    out << "((_ extract "
           << (width-1)
           << " 0) ";
    convert_expr(struct_op);
    out << ")";

    unflatten(END, expr.type());
  }
  else
    UNEXPECTEDCASE("convert_member on an unexpected type " + struct_op_type.id_string());
}

/*******************************************************************\

Function: smt2_convt::flatten2bv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      assert(datatype_map.find(type) != datatype_map.end());

      const std::string smt_typename=
        datatype_map.find(type)->second;

      // concatenate elements
      const vector_typet &vector_type=to_vector_type(type);
      
      mp_integer size;
      if(to_integer(vector_type.size(), size))
        INVALIDEXPR("failed to convert vector size to constant");
        
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
      assert(datatype_map.find(type) != datatype_map.end());

      const std::string smt_typename=
        datatype_map.find(type)->second;

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
    if(use_FPA_theory)
      INVALIDEXPR("need to flatten floatbv in FPA theory");
    else
      convert_expr(expr); // good as is
  }
  else
    convert_expr(expr);
}

/*******************************************************************\

Function: smt2_convt::unflatten

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::unflatten(
  wheret where,
  const typet &type,
  unsigned nesting)
{
  if(type.id()==ID_symbol)
    return unflatten(where, ns.follow(type));
    
  if(type.id()==ID_bool)
  {
    if(where==BEGIN)
      out << "(= "; // produces a bool
    else
      out << " #b1)";
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      assert(datatype_map.find(type) != datatype_map.end());

      const std::string smt_typename=
        datatype_map.find(type)->second;

      // extract elements
      const vector_typet &vector_type=to_vector_type(type);
      
      std::size_t subtype_width=boolbv_width(vector_type.subtype());
      
      mp_integer size;
      if(to_integer(vector_type.size(), size))
        INVALIDEXPR("failed to convert vector size to constant");

      if(where==BEGIN)
        out << "(let ((?ufop" << nesting << " ";
      else
      {
        out << ")) ";
        
        out << "(mk-" << smt_typename;

        std::size_t offset=0;

        for(mp_integer i=0; i!=size; ++i, offset+=subtype_width)
        {
          out << " ";
	  unflatten(BEGIN, vector_type.subtype(), nesting+1);
          out << "((_ extract " << offset+subtype_width-1 << " "
              << offset << ") ?ufop" << nesting << ")";
          unflatten(END, vector_type.subtype(), nesting+1);
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
      if(where==BEGIN)
        out << "(let ((?ufop" << nesting << " ";
      else
      {
        out << ")) ";
        
        assert(datatype_map.find(type) != datatype_map.end());

        const std::string smt_typename=
          datatype_map.find(type)->second;

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
          unflatten(BEGIN, it->type(), nesting+1);
          out << "((_ extract " << offset+member_width-1 << " "
              << offset << ") ?ufop" << nesting << ")";
          unflatten(END, it->type(), nesting+1);
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

/*******************************************************************\

Function: smt2_convt::convert_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_overflow(const exprt &expr)
{
  UNREACHABLE;
}

/*******************************************************************\

Function: smt2_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::set_to(const exprt &expr, bool value)
{
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
    assert(expr.operands().size()==1);
    return set_to(expr.op0(), !value);
  }

  out << "\n";

  assert(expr.type().id()==ID_bool);
  
  // special treatment for "set_to(a=b, true)" where
  // a is a new symbol

  if(expr.id()==ID_equal && value==true)
  {
    const equal_exprt &equal_expr=to_equal_expr(expr);

    if(equal_expr.lhs().id()==ID_symbol)
    {
      const irep_idt &identifier=to_symbol_expr(equal_expr.lhs()).get_identifier();
      
      if(identifier_map.find(identifier)==identifier_map.end())
      {
        identifiert &id=identifier_map[identifier];

        assert(id.type.is_nil());

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
      << from_expr(expr) << "\n";
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

/*******************************************************************\

Function: smt2_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      identifier="nondet_"+id2string(expr.get(ID_identifier));

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
      irep_idt id="array_of."+i2string(defined_expressions.size());
      out << "; the following is a substitute for lambda i. x" << "\n";
      out << "(declare-fun " << id << " () ";
      convert_type(expr.type());
      out << ")" << "\n";

      // use a quantifier instead of the lambda
      #if 0 // not really working in any sover yet!
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
    
      irep_idt id="array."+i2string(defined_expressions.size());
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

      irep_idt id="string."+i2string(defined_expressions.size());
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

    if (op.type().id() == ID_pointer ||
        op.type().id() == ID_reference)
    {
      if (object_sizes.find(expr)==object_sizes.end())
      {
        irep_idt id="object_size."+i2string(object_sizes.size());
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

      for(unsigned i=0; i<expr.operands().size(); i++)
      {
        if(i!=0) out << " ";
        out << "(op" << i << ' ';
        convert_type(expr.operands()[i].type());
        out << ')';
      }
      
      out << ") ";
      convert_type(expr.type()); // return type
      out << ' ';
      
      exprt tmp1=expr;
      for(unsigned i=0; i<tmp1.operands().size(); i++)
        tmp1.operands()[i]=
          smt2_symbolt("op"+i2string(i), tmp1.operands()[i].type());

      exprt tmp2=float_bv(tmp1);
      tmp2=letify(tmp2);

      assert(!tmp2.is_nil());
      convert_expr(tmp2);

      out << ")\n"; // define-fun
    }
  }

}

/*******************************************************************\

Function: smt2_convt::use_array_theory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smt2_convt::use_array_theory(const exprt &expr)
{
  const typet &type=ns.follow(expr.type());
  assert(type.id()==ID_array);
  //const array_typet &array_type=to_array_type(ns.follow(expr.type()));
  
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

/*******************************************************************\

Function: smt2_convt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    // we always use array theory for top-level arrays
    const typet &subtype=ns.follow(array_type.subtype());

    out << "(Array ";
    assert(array_type.size().is_not_nil());
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
      assert(datatype_map.find(type)!=datatype_map.end());
      out << datatype_map.find(type)->second;
    }
    else
    {
      std::size_t width=boolbv_width(type);
      
      if(width==0)
        INVALIDEXPR("failed to get width of struct");

      out << "(_ BitVec " << width << ")";
    }
  }
  else if(type.id()==ID_vector)
  {
    if(use_datatypes)
    {
      assert(datatype_map.find(type)!=datatype_map.end());
      out << datatype_map.find(type)->second;
    }
    else
    {
      boolbv_widtht boolbv_width(ns);
    
      std::size_t width=boolbv_width(type);
      
      if(width==0)
        INVALIDEXPR("failed to get width of vector");

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
    
    if(width==0)
      INVALIDEXPR("failed to get width of union");

    out << "(_ BitVec " << width << ")";
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_reference)
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
  else if(type.id()==ID_rational)
    out << "Real";
  else if(type.id()==ID_integer)
    out << "Int";
  else if(type.id()==ID_symbol)
    convert_type(ns.follow(type));
  else if(type.id()==ID_complex)
  {
    if(use_datatypes)
    {
      assert(datatype_map.find(type)!=datatype_map.end());
      out << datatype_map.find(type)->second;
    }
    else
    {
      boolbv_widtht boolbv_width(ns);
    
      std::size_t width=boolbv_width(type);
      
      if(width==0)
        INVALIDEXPR("failed to get width of complex");

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

/*******************************************************************\

Function: smt2_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::find_symbols(const typet &type)
{
  std::set<irep_idt> recstack;
  find_symbols_rec(type, recstack);
}

/*******************************************************************\

Function: smt2_convt::find_symbols_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
       std::string smt_typename = "complex."+i2string(datatype_map.size());
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
      
       mp_integer size;
       if(to_integer(vector_type.size(), size))
         INVALIDEXPR("failed to convert vector size to constant");

       std::string smt_typename = "vector."+i2string(datatype_map.size());
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
       std::string smt_typename = "struct."+i2string(datatype_map.size());
       datatype_map[type] = smt_typename;
       need_decl=true;
     }

     const struct_typet::componentst &components=
       to_struct_type(type).components();

     for(std::size_t i=0; i<components.size(); i++)
       find_symbols_rec(components[i].type(), recstack);

     // Declare the corresponding SMT type if we haven't already.
     if(need_decl)
     {
       std::string smt_typename = datatype_map[type];

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

       for(std::size_t i = 0; i < components.size(); i++)
       {
         const struct_union_typet::componentt &component = components[i];
         out << "(" << smt_typename << "." << component.get_name()
                       << " ";
         convert_type(component.type());
         out << ") ";
       }

       out << "))))" << "\n";

       // Let's also declare convenience functions to update individual members of
       // the struct whil we're at it.  The functions are named like
       // `update-struct.0.component1'.  Their declarations look like:
       //
       // (declare-fun update-struct.0.component1
       //               ((s struct.0)     ; first arg -- the struct to update
       //                (v type1))       ; second arg -- the value to update
       //               struct.0          ; the output type
       //               (mk-struct.0      ; build the new struct...
       //                v                ; the updated value
       //                (struct.0.component2 s)  ; retain the other members
       //                ...
       //                (struct.0.componentN s)))

       for(std::size_t i = 0; i < components.size(); i++)
       {
         const struct_union_typet::componentt &component = components[i];
         out << "(define-fun update-" << smt_typename << "."
             << component.get_name() << " "
             << "((s " << smt_typename << ") "
             <<  "(v ";
         convert_type(component.type());
         out << ")) " << smt_typename << " "
             << "(mk-" << smt_typename
             << " ";

         for(std::size_t j = 0; j < components.size(); j++)
         {
           if(j==i)
             out << "v ";
           else
           {
             out << "(" << smt_typename << "."
                 << components[j].get_name() << " s) ";
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

     for(std::size_t i=0; i<components.size(); i++)
       find_symbols_rec(components[i].type(), recstack);
   }
   else if(type.id()==ID_code)
   {
     const code_typet::parameterst &parameters=
         to_code_type(type).parameters();
     for(std::size_t i=0; i<parameters.size(); i++)
       find_symbols_rec(parameters[i].type(), recstack);

     find_symbols_rec(to_code_type(type).return_type(), recstack);
   }
   else if(type.id()==ID_pointer)
   {
     find_symbols_rec(type.subtype(), recstack);
   }
   else if(type.id()==ID_symbol)
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

/*******************************************************************\

Function: smt2_convt::letify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::letify(exprt &expr)
{
  seen_expressionst map;
  std::vector<exprt> let_order;

  collect_bindings(expr, map, let_order);

  return letify_rec(expr, let_order, map, 0);
}

/*******************************************************************\

Function: smt2_convt::letify_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smt2_convt::letify_rec(
  exprt &expr,
  std::vector<exprt> &let_order,
  const seen_expressionst &map,
  unsigned i)
{
  if(i >= let_order.size())
    return substitute_let(expr, map);

  exprt current=let_order[i];
  assert(map.find(current) != map.end());
  
  if (map.find(current)->second.first < LET_COUNT)
    return letify_rec(expr, let_order, map, i+1);

  let_exprt let;

  let.symbol() = map.find(current)->second.second;
  let.value() = substitute_let(current, map);
  let.where() = letify_rec(expr, let_order, map, i+1);

  return let;
}

/*******************************************************************\

Function: smt2_convt::collect_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt2_convt::collect_bindings(
  exprt &expr,
  seen_expressionst &map,
  std::vector<exprt> &let_order)
{
  seen_expressionst::iterator it = map.find(expr);

  if(it!=map.end())
  {
    let_count_id &count_id = it->second;
    ++(count_id.first);
    return;
  }

  // do not letify things with no children
  if(expr.operands().empty())
    return;
  
  for (unsigned i = 0; i < expr.operands().size(); ++i)
    collect_bindings(expr.operands()[i], map, let_order);

  assert(map.find(expr) == map.end());

  symbol_exprt let=
    symbol_exprt("_let_"+i2string(++let_id_count), expr.type());

  map.insert(std::make_pair(expr, std::make_pair(1, let)));

  let_order.push_back(expr);
}

/*******************************************************************\

Function: smt2_convt::substitute_let

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
