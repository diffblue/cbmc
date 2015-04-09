/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cctype>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/config.h>
#include <util/i2string.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/pointer_offset_size.h>
#include <util/string2int.h>

#include <ansi-c/string_constant.h>

#include "cvc_conv.h"

/*******************************************************************\

Function: cvc_convt::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::print_assignment(std::ostream &out) const
{
  // Boolean stuff
  
  for(unsigned v=0; v<boolean_assignment.size(); v++)
    out << "b" << v << "=" << boolean_assignment[v] << "\n";

  // others
}

/*******************************************************************\

Function: cvc_convt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt cvc_convt::l_get(literalt l) const
{
  if(l.is_true()) return tvt(true);
  if(l.is_false()) return tvt(false);
  assert(l.var_no()<boolean_assignment.size());
  return tvt(boolean_assignment[l.var_no()]^l.sign());
}

/*******************************************************************\

Function: cvc_convt::convert_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_literal(const literalt l)
{
  if(l==const_literal(false))
    out << "FALSE";
  else if(l==const_literal(true))
    out << "TRUE";

  if(l.sign())
    out << "(NOT ";
  
  out << "l" << l.var_no();

  if(l.sign())
    out << ")";
}

/*******************************************************************\

Function: cvc_convt::bin_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cvc_convt::bin_zero(unsigned bits)
{
  assert(bits!=0);
  std::string result="0bin";
  while(bits!=0) { result+='0'; bits--; }
  return result;
}

/*******************************************************************\

Function: cvc_convt::cvc_pointer_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cvc_convt::cvc_pointer_type()
{
  assert(config.ansi_c.pointer_width!=0);
  return "[# object: INT, offset: BITVECTOR("+
         i2string(config.ansi_c.pointer_width)+") #]";
}

/*******************************************************************\

Function: cvc_convt::array_index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cvc_convt::array_index_type()
{
  return std::string("BITVECTOR(")+
         i2string(32)+")";
}

/*******************************************************************\

Function: cvc_convt::gen_array_index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet cvc_convt::gen_array_index_type()
{
  typet t(ID_signedbv);
  t.set(ID_width, 32);
  return t;
}

/*******************************************************************\

Function: cvc_convt::array_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cvc_convt::array_index(unsigned i)
{
  return "0bin"+integer2binary(i, config.ansi_c.int_width);
}

/*******************************************************************\

Function: cvc_convt::convert_array_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_array_index(const exprt &expr)
{
  if(expr.type()==gen_array_index_type())
  {
    convert_expr(expr);
  }
  else
  {
    exprt tmp(ID_typecast, gen_array_index_type());
    tmp.copy_to_operands(expr);
    convert_expr(tmp);
  }
}

/*******************************************************************\

Function: cvc_convt::convert_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_address_of_rec(const exprt &expr)
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_constant ||
     expr.id()==ID_string_constant)
  {
    out
      << "(# object:="
      << pointer_logic.add_object(expr)
      << ", offset:="
      << bin_zero(config.ansi_c.pointer_width) << " #)";
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index takes two operands";

    const exprt &array=expr.op0();
    const exprt &index=expr.op1();

    if(index.is_zero())
    {
      if(array.type().id()==ID_pointer)
        convert_expr(array);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array);
      else
        assert(false);
    }
    else
    {    
      out << "(LET P: ";
      out << cvc_pointer_type();
      out << " = ";
      
      if(array.type().id()==ID_pointer)
        convert_expr(array);
      else if(array.type().id()==ID_array)
        convert_address_of_rec(array);
      else
        assert(false);

      out << " IN P WITH .offset:=BVPLUS("
                   << config.ansi_c.pointer_width
                   << ", P.offset, ";
      convert_expr(index);
      out << "))";
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()!=1)
      throw "member takes one operand";

    const exprt &struct_op=expr.op0();

    out << "(LET P: ";
    out << cvc_pointer_type();
    out << " = ";
    
    convert_address_of_rec(struct_op);

    const irep_idt &component_name=
      to_member_expr(expr).get_component_name();
      
    mp_integer offset=member_offset(
      to_struct_type(struct_op.type()),
      component_name, ns);
    
    typet index_type(ID_unsignedbv);
    index_type.set(ID_width, config.ansi_c.pointer_width);

    exprt index=from_integer(offset, index_type);

    out << " IN P WITH .offset:=BVPLUS("
                 << config.ansi_c.pointer_width
                 << ", P.offset, ";
    convert_expr(index);
    out << "))";
  }
  else
    throw "don't know how to take address of: "+expr.id_string();
}

/*******************************************************************\

Function: cvc_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_convt::convert(const exprt &expr)
{
  //out << "%% E: " << expr << std::endl;

  if(expr.type().id()!=ID_bool)
  {
    std::string msg="cvc_convt::convert got "
                    "non-boolean expression:\n";
    msg+=expr.to_string();
    throw msg;
  }

  // Three special cases in which we don't need to generate
  // a handle.
  
  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);
  else if(expr.id()==ID_literal)
    return to_literal_expr(expr).get_literal();

  // Generate new handle

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;
  
  find_symbols(expr);

  // define new handle
  out << "ASSERT ";
  convert_literal(l);
  out << " <=> (";
  convert_expr(expr);
  out << ");" << std::endl << std::endl;

  return l;
}

/*******************************************************************\

Function: cvc_convt::convert_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_identifier(const std::string &identifier)
{
  for(std::string::const_iterator
      it=identifier.begin();
      it!=identifier.end();
      it++)
  {
    char ch=*it;

    if(isalnum(ch) || ch=='$' || ch=='?')
      out << ch;
    else if(ch==':')
    {
      std::string::const_iterator next_it(it);
      next_it++;
      if(next_it!=identifier.end() && *next_it==':')
      {
        out << "__";
        it=next_it;
      }
      else
      {
        out << '_';
        out << int(ch);
        out << '_';
      }
    }
    else
    {
      out << '_';
      out << int(ch);
      out << '_';
    }
  }
}

/*******************************************************************\

Function: cvc_convt::convert_as_bv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_as_bv(const exprt &expr)
{
  if(expr.type().id()==ID_bool)
  {
    if(expr.is_true())
      out << "0bin1";
    else if(expr.is_false())
      out << "0bin0";
    else
    {
      out << "IF ";
      convert_expr(expr);
      out << " THEN 0bin1 ELSE 0bin0 ENDIF";
    }
  }
  else
    convert_expr(expr);
}

/*******************************************************************\

Function: cvc_convt::convert_array_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_array_value(const exprt &expr)
{
  convert_as_bv(expr);
}

/*******************************************************************\

Function: cvc_convt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_expr(const exprt &expr)
{
  const exprt::operandst &op=expr.operands();

  if(expr.id()==ID_implies)
  {
    if(op.size()!=2)
      throw "implication takes two operands";

    out << "(";
    convert_expr(op[0]);
    out << ") => (";
    convert_expr(op[1]);
    out << ")";
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    if(op.size()<2)
      throw "constraint_select_one takes at least two operands";

    // TODO
    throw "cvc_convt::convert_expr needs constraint_select_one";
  }
  else if(expr.id()==ID_or || expr.id()==ID_and || expr.id()==ID_xor ||
          expr.id()==ID_nor || expr.id()==ID_nand)
  {
    if(op.empty())
      throw "operator `"+expr.id_string()+"' takes at least one operand";
    else if(op.size()==1)
      convert_expr(op[0]);
    else
    {
      forall_expr(it, op)
      {
        if(it!=op.begin())
        {
          if(expr.id()==ID_or)
            out << " OR ";
          else if(expr.id()==ID_nor)
            out << " NOR ";
          else if(expr.id()==ID_and)
            out << " AND ";
          else if(expr.id()==ID_nand)
            out << " NAND ";
          else if(expr.id()==ID_xor) 
            out << " XOR ";
          else
            assert(false);
        }

        out << "(";
        convert_expr(*it);
        out << ")";
      }
    }
  }
  else if(expr.id()==ID_not)
  {
    if(op.size()!=1)
      throw "not takes one operand";

    out << "NOT (";
    convert_expr(op[0]);
    out << ")";
  }
  else if(expr.id()==ID_symbol)
  {
    convert_identifier(expr.get_string(ID_identifier));
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    convert_identifier("nondet$"+expr.get_string(ID_identifier));
  }
  else if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    const exprt &op=expr.op0();
    
    if(expr.type().id()==ID_bool)
    {
      if(op.type().id()==ID_signedbv ||
         op.type().id()==ID_unsignedbv ||
         op.type().id()==ID_pointer)
      {
        convert_expr(op);
        out << "/=";
        convert_expr(gen_zero(op.type()));
      }
      else
      {
        throw "TODO typecast1 "+op.type().id_string()+" -> bool";
      }
    }
    else if(expr.type().id()==ID_signedbv ||
            expr.type().id()==ID_unsignedbv)
    {
      unsigned to_width=unsafe_string2unsigned(id2string(expr.type().get(ID_width)));
      
      if(op.type().id()==ID_signedbv)
      {
        unsigned from_width=unsafe_string2unsigned(id2string(op.type().get(ID_width)));
        
        if(from_width==to_width)
          convert_expr(op);
        else if(from_width<to_width)
        {
          out << "SX(";
          convert_expr(op);
          out << ", " << to_width << ")";
        }
        else
        {
          out << "(";
          convert_expr(op);
          out << ")[" << (to_width-1) << ":0]";
        }
      }
      else if(op.type().id()==ID_unsignedbv)
      {
        unsigned from_width=unsafe_string2unsigned(id2string(op.type().get(ID_width)));
        
        if(from_width==to_width)
          convert_expr(op);
        else if(from_width<to_width)
        {
          out << "(0bin";

          for(unsigned i=from_width; i<to_width; i++)
            out << "0";

          out << " @ ";
            
          out << "(";
          convert_expr(op);
          out << "))";
        }
        else
        {
          out << "(";
          convert_expr(op);
          out << ")[" << (to_width-1) << ":0]";
        }
      }
      else if(op.type().id()==ID_bool)
      {
        if(to_width>1)
        {
          out << "(0bin";

          for(unsigned i=1; i<to_width; i++)
            out << "0";

          out << " @ ";
          
          out << "IF ";
          convert_expr(op);
          out << " THEN 0bin1 ELSE 0bin0 ENDIF)";
        }
        else
        {
          out << "IF ";
          convert_expr(op);
          out << " THEN 0bin1 ELSE 0bin0 ENDIF";
        }
      }
      else
      {
        throw "TODO typecast2 "+op.type().id_string()+
              " -> "+expr.type().id_string();
      }
    }
    else if(expr.type().id()==ID_pointer)
    {
      if(op.type().id()==ID_pointer)
      {
        convert_expr(op);
      }
      else
        throw "TODO typecast3 "+op.type().id_string()+" -> pointer";
    }
    else
      throw "TODO typecast4 ? -> "+expr.type().id_string();
  }
  else if(expr.id()==ID_struct)
  {
    out << "(# ";
    
    const struct_typet &struct_type=to_struct_type(expr.type());
  
    const struct_typet::componentst &components=
      struct_type.components();
      
    assert(components.size()==expr.operands().size());

    unsigned i=0;
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++, i++)
    {
      if(i!=0) out << ", ";
      out << it->get(ID_name);
      out << ":=";
      convert_expr(expr.operands()[i]);
    }
    
    out << " #)";
  }
  else if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_bv)
    {
      const irep_idt &value=expr.get(ID_value);
      
      if(value.size()==8 ||
         value.size()==16 ||
         value.size()==32 ||
         value.size()==64)
      {
        unsigned w=value.size()/4;
      
        mp_integer i=binary2integer(id2string(value), false);
        std::string hex=integer2string(i, 16);
        
        while(hex.size()<w) hex="0"+hex;
        
        out << "0hex" << hex;
      }
      else
      {
        out << "0bin" << value;
      }
    }
    else if(expr.type().id()==ID_pointer)
    {
      const irep_idt &value=expr.get(ID_value);
      
      if(value=="NULL")
      {
        out << "(# object:="
                     << pointer_logic.get_null_object()
                     << ", offset:="
                     << bin_zero(config.ansi_c.pointer_width) << " #)";
      }
      else
        throw "unknown pointer constant: "+id2string(value);
    }
    else if(expr.type().id()==ID_bool)
    {
      if(expr.is_true())
        out << "TRUE";
      else if(expr.is_false())
        out << "FALSE";
      else
        throw "unknown boolean constant";
    }
    else if(expr.type().id()==ID_array)
    {
      out << "ARRAY (i: " << array_index_type() << "):";
      
      assert(!expr.operands().empty());
      
      unsigned i=0;
      forall_operands(it, expr)
      {
        if(i==0)
          out << "\n  IF ";
        else
          out << "\n  ELSIF ";

        out << "i=" << array_index(i) << " THEN ";
        convert_array_value(*it);
        i++;
      }
      
      out << "\n  ELSE ";
      convert_expr(expr.op0());
      out << "\n  ENDIF";
    }
    else if(expr.type().id()==ID_integer ||
            expr.type().id()==ID_natural ||
            expr.type().id()==ID_range)
    {
      out << expr.get(ID_value);
    }
    else
      throw "unknown constant: "+expr.type().id_string();
  }
  else if(expr.id()==ID_concatenation || 
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor)
  {
    out << "(";

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
      {
        if(expr.id()==ID_concatenation)
          out << " @ ";
        else if(expr.id()==ID_bitand)
          out << " & ";
        else if(expr.id()==ID_bitor)
          out << " | ";
      }

      convert_as_bv(*it);
    }

    out << ")";
  }
  else if(expr.id()==ID_bitxor)
  {
    assert(!expr.operands().empty());
  
    if(expr.operands().size()==1)
    {
      convert_expr(expr.op0());
    }
    else if(expr.operands().size()==2)
    {
      out << "BVXOR(";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
    {
      assert(expr.operands().size()>=3);
      
      exprt tmp(expr);
      tmp.operands().resize(tmp.operands().size()-1);

      out << "BVXOR(";
      convert_expr(tmp);
      out << ", ";
      convert_expr(expr.operands().back());
      out << ")";
    }
  }
  else if(expr.id()==ID_bitnand)
  {
    assert(expr.operands().size()==2);

    out << "BVNAND(";
    convert_expr(expr.op0());
    out << ", ";
    convert_expr(expr.op1());
    out << ")";
  }
  else if(expr.id()==ID_bitnot)
  {
    assert(expr.operands().size()==1);
    out << "~(";
    convert_expr(expr.op0());
    out << ")";
  }
  else if(expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);
    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      out << "BVUMINUS(";
      convert_expr(expr.op0());
      out << ")";
    }
    else
      throw "unsupported type for unary-: "+expr.type().id_string();
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    out << "IF ";
    convert_expr(expr.op0());
    out << " THEN ";
    convert_expr(expr.op1());
    out << " ELSE ";
    convert_expr(expr.op2());
    out << " ENDIF";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    
    if(expr.operands().size()>=2)
    {
      forall_operands(it, expr)
      {
        if(it!=expr.operands().begin())
        {
          if(expr.id()==ID_and)
            out << " AND ";
          else if(expr.id()==ID_or)
            out << " OR ";
          else if(expr.id()==ID_xor)
            out << " XOR ";
        }
        
        out << "(";
        convert_expr(*it);
        out << ")";
      }
    }
    else if(expr.operands().size()==1)
    {
      convert_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    out << "NOT (";
    convert_expr(expr.op0());
    out << ")";
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(expr.op0().type()==expr.op1().type());

    if(expr.op0().type().id()==ID_bool)
    {
      if(expr.id()==ID_notequal) out << "NOT (";
      out << "(";
      convert_expr(expr.op0());
      out << ") <=> (";
      convert_expr(expr.op1());
      out << ")";
      if(expr.id()==ID_notequal) out << ")";
    }
    else
    {
      out << "(";
      convert_expr(expr.op0());
      out << ")";
      out << (expr.id()==ID_equal?"=":"/=");
      out << "(";
      convert_expr(expr.op1());
      out << ")";
    }
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    assert(expr.operands().size()==2);
    
    const typet &op_type=expr.op0().type();

    if(op_type.id()==ID_unsignedbv)
    {
      if(expr.id()==ID_le)
        out << "BVLE";
      else if(expr.id()==ID_lt)
        out << "BVLT";
      else if(expr.id()==ID_ge)
        out << "BVGE";
      else if(expr.id()==ID_gt)
        out << "BVGT";
      
      out << "(";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else if(op_type.id()==ID_signedbv)
    {
      if(expr.id()==ID_le)
        out << "SBVLE";
      else if(expr.id()==ID_lt)
        out << "SBVLT";
      else if(expr.id()==ID_ge)
        out << "SBVGE";
      else if(expr.id()==ID_gt)
        out << "SBVGT";
      
      out << "(";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.type().id_string();
  }
  else if(expr.id()==ID_plus)
  {
    if(expr.operands().size()>=2)
    {
      if(expr.type().id()==ID_unsignedbv ||
         expr.type().id()==ID_signedbv)
      {
        out << "BVPLUS(" << expr.type().get(ID_width);

        forall_operands(it, expr)
        {
          out << ", ";
          convert_expr(*it);
        }
          
        out << ")";
      }
      else if(expr.type().id()==ID_pointer)
      {
        if(expr.operands().size()!=2)
          throw "pointer arithmetic with more than two operands";
        
        const exprt *p, *i;
        
        if(expr.op0().type().id()==ID_pointer)
        {
          p=&expr.op0();
          i=&expr.op1();
        }
        else if(expr.op1().type().id()==ID_pointer)
        {
          p=&expr.op1();
          i=&expr.op0();
        }
        else
          throw "unexpected mixture in pointer arithmetic";
        
        out << "(LET P: " << cvc_pointer_type() << " = ";
        convert_expr(*p);
        out << " IN P WITH .offset:=BVPLUS("
                     << config.ansi_c.pointer_width
                     << ", P.offset, ";
        convert_expr(*i);
        out << "))";
      }
      else
        throw "unsupported type for +: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()==ID_minus)
  {
    if(expr.operands().size()==2)
    {
      if(expr.type().id()==ID_unsignedbv ||
         expr.type().id()==ID_signedbv)
      {
        out << "BVSUB(" << expr.type().get(ID_width) << ", ";
        convert_expr(expr.op0());
        out << ", ";
        convert_expr(expr.op1());
        out << ")";
      }
      else
        throw "unsupported type for -: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      if(expr.type().id()==ID_unsignedbv)
        out << "BVDIV";
      else
        out << "SBVDIV";

      out << "(" << expr.type().get(ID_width) << ", ";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
      throw "unsupported type for /: "+expr.type().id_string();
  }
  else if(expr.id()==ID_mod)
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      if(expr.type().id()==ID_unsignedbv)
        out << "BVMOD";
      else
        out << "SBVMOD";

      out << "(" << expr.type().get(ID_width) << ", ";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
      throw "unsupported type for mod: "+expr.type().id_string();
  }
  else if(expr.id()==ID_mult)
  {
    if(expr.operands().size()==2)
    {
      if(expr.type().id()==ID_unsignedbv ||
         expr.type().id()==ID_signedbv)
      {
        out << "BVMULT(" << expr.type().get(ID_width) << ", ";
        convert_expr(expr.op0());
        out << ", ";
        convert_expr(expr.op1());
        out << ")";
      }
      else
        throw "unsupported type for *: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()==ID_address_of ||
          expr.id()=="implicit_address_of" ||
          expr.id()=="reference_to")
  {
    assert(expr.operands().size()==1);
    assert(expr.type().id()==ID_pointer);
    convert_address_of_rec(expr.op0());
  }
  else if(expr.id()==ID_array_of)
  {
    assert(expr.type().id()==ID_array);
    assert(expr.operands().size()==1);
    out << "(ARRAY (i: " << array_index_type() << "): ";
    convert_array_value(expr.op0());
    out << ")";
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    out << "(";
    convert_expr(expr.op0());
    out << ")[";
    convert_array_index(expr.op1());
    out << "]";
  }
  else if(expr.id()==ID_ashr ||
          expr.id()==ID_lshr ||
          expr.id()==ID_shl)
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      if(expr.id()==ID_ashr)
        out << "BVASHR";
      else if(expr.id()==ID_lshr)
        out << "BVLSHR";
      else if(expr.id()==ID_shl)
        out << "BVSHL";
      else
        assert(false);

      out << "(" << expr.type().get(ID_width) << ", ";
      convert_expr(expr.op0());
      out << ", ";
      convert_expr(expr.op1());
      out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.type().id_string();
  }
  else if(expr.id()==ID_with)
  {
    assert(expr.operands().size()>=1);
    out << "(";
    convert_expr(expr.op0());
    out << ")";
  
    for(unsigned i=1; i<expr.operands().size(); i+=2)
    {
      assert((i+1)<expr.operands().size());
      const exprt &index=expr.operands()[i];
      const exprt &value=expr.operands()[i+1];

      if(expr.type().id()==ID_struct)
      {
        out << " WITH ." << index.get(ID_component_name);
        out << ":=(";
        convert_array_value(value);
        out << ")";
      }
      else if(expr.type().id()==ID_union)
      {
        out << " WITH ." << index.get(ID_component_name);
        out << ":=(";
        convert_array_value(value);
        out << ")";
      }
      else if(expr.type().id()==ID_array)
      {
        out << " WITH [";
        convert_array_index(index);
        out << "]:=(";
        convert_array_value(value);
        out << ")";
      }
      else
        throw "with expects struct or array type, but got "+expr.type().id_string();
    }
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    convert_expr(expr.op0());
    out << ".";
    out << expr.get(ID_component_name);
  }
  else if(expr.id()==ID_pointer_offset)
  {
    assert(expr.operands().size()==1);
    out << "(";
    convert_expr(expr.op0());
    out << ").offset";
  }
  #if 0
  else if(expr.id()==ID_pointer_object)
  {
    assert(expr.operands().size()==1);
    out << "(";
    convert_expr(expr.op0());
    out << ").object";
    // TODO, this has the wrong type
  }
  #endif
  else if(expr.id()==ID_string_constant)
  {
    convert_expr(to_string_constant(expr).to_array_expr());
  }
  else if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op0().type().id()==ID_unsignedbv ||
       expr.op0().type().id()==ID_signedbv)
    {
      out << "(";
      convert_expr(expr.op0());
      
      mp_integer i;
      if(to_integer(expr.op1(), i))
        throw "extractbit takes constant as second parameter";
        
      out << "[" << i << ":" << i << "]=0bin1)";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.op0().type().id_string();
  }
  else if(expr.id()==ID_replication)
  {
    assert(expr.operands().size()==2);
  
    mp_integer times;
    if(to_integer(expr.op0(), times))
      throw "replication takes constant as first parameter";
    
    out << "(LET v: BITVECTOR(1) = ";

    convert_expr(expr.op1());

    out << " IN ";

    for(mp_integer i=0; i<times; ++i)
    {
      if(i!=0) out << "@";
      out << "v";
    }
    
    out << ")";
  }
  else
    throw "convert_expr: "+expr.id_string()+" is unsupported";
}

/*******************************************************************\

Function: cvc_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::set_to(const exprt &expr, bool value)
{
  if(value && expr.id()==ID_and)
  {
    forall_operands(it, expr)
      set_to(*it, true);
    return;
  }
  
  out << "%% set_to " << (value?"true":"false") << std::endl;

  if(expr.id()==ID_equal && value)
  {
    assert(expr.operands().size()==2);
    
    if(expr.op0().id()==ID_symbol)
    {
      const irep_idt &identifier=expr.op0().get(ID_identifier);
      
      identifiert &id=identifier_map[identifier];

      if(id.type.is_nil())
      {
        hash_set_cont<irep_idt, irep_id_hash> s_set;

        ::find_symbols(expr.op1(), s_set);

        if(s_set.find(identifier)==s_set.end())
        {
          id.type=expr.op0().type();

          find_symbols(expr.op1());

          convert_identifier(id2string(identifier));
          out << ": ";
          convert_type(expr.op0().type());
          out << " = ";
          convert_expr(expr.op1());
        
          out << ";" << std::endl << std::endl;
          return;
        }
      }
    }
  }
  
  find_symbols(expr);

  out << "ASSERT ";

  if(!value)
    out << "NOT (";
    
  convert_expr(expr);

  if(!value)
    out << ")";
    
  out << ";" << std::endl << std::endl;
}

/*******************************************************************\

Function: cvc_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::find_symbols(const exprt &expr)
{
  find_symbols(expr.type());

  forall_operands(it, expr)
    find_symbols(*it);
    
  if(expr.id()==ID_symbol)
  {
    if(expr.type().id()==ID_code)
      return;

    const irep_idt &identifier=expr.get(ID_identifier);

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      convert_identifier(id2string(identifier));
      out << ": ";
      convert_type(expr.type());
      out << ";" << std::endl;
    }
  }  
  else if(expr.id()==ID_nondet_symbol)
  {
    if(expr.type().id()==ID_code)
      return;

    const irep_idt identifier="nondet$"+expr.get_string(ID_identifier);

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      convert_identifier(id2string(identifier));
      out << ": ";
      convert_type(expr.type());
      out << ";" << std::endl;
    }
  }  
}

/*******************************************************************\

Function: cvc_convt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_type(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    
    out << "ARRAY " << array_index_type()
                 << " OF ";
                 
    if(array_type.subtype().id()==ID_bool)
      out << "BITVECTOR(1)";
    else
      convert_type(array_type.subtype());
  }
  else if(type.id()==ID_bool)
  {
    out << "BOOLEAN";
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    const struct_typet &struct_type=to_struct_type(type);
  
    out << "[#";
    
    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it!=components.begin()) out << ",";
      out << " ";
      out << it->get(ID_name);
      out << ": ";
      convert_type(it->type());
    }
    
    out << " #]";
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_reference)
  {
    out << cvc_pointer_type();
  }
  else if(type.id()==ID_integer)
  {
    out << "INT";
  }
  else if(type.id()==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();
      
    if(width==0)
      throw "zero-width vector type: "+type.id_string();
  
    out << "BITVECTOR(" << width << ")";
  }
  else if(type.id()==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();
      
    if(width==0)
      throw "zero-width vector type: "+type.id_string();
  
    out << "BITVECTOR(" << width << ")";
  }
  else
    throw "unsupported type: "+type.id_string();
}    

/*******************************************************************\

Function: cvc_convt::find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::find_symbols(const typet &type)
{
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    find_symbols(array_type.size());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
  }
}
