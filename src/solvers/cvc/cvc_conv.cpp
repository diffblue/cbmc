/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <ctype.h>
#include <cstdlib>

#include <arith_tools.h>
#include <std_types.h>
#include <std_expr.h>
#include <config.h>
#include <i2string.h>
#include <expr_util.h>
#include <find_symbols.h>
#include <pointer_offset_size.h>

#include <ansi-c/string_constant.h>

#include "cvc_conv.h"

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
  typet t("signedbv");
  t.set("width", 32);
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
    convert_cvc_expr(expr);
  }
  else
  {
    exprt tmp("typecast", gen_array_index_type());
    tmp.copy_to_operands(expr);
    convert_cvc_expr(tmp);
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
  if(expr.id()=="symbol" ||
     expr.id()=="constant" ||
     expr.id()==ID_string_constant)
  {
    cvc_prop.out
      << "(# object:="
      << pointer_logic.add_object(expr)
      << ", offset:="
      << bin_zero(config.ansi_c.pointer_width) << " #)";
  }
  else if(expr.id()=="index")
  {
    if(expr.operands().size()!=2)
      throw "index takes two operands";

    const exprt &array=expr.op0();
    const exprt &index=expr.op1();

    if(index.is_zero())
    {
      if(array.type().id()=="pointer")
        convert_cvc_expr(array);
      else if(array.type().id()=="array")
        convert_address_of_rec(array);
      else
        assert(false);
    }
    else
    {    
      cvc_prop.out << "(LET P: ";
      cvc_prop.out << cvc_pointer_type();
      cvc_prop.out << " = ";
      
      if(array.type().id()=="pointer")
        convert_cvc_expr(array);
      else if(array.type().id()=="array")
        convert_address_of_rec(array);
      else
        assert(false);

      cvc_prop.out << " IN P WITH .offset:=BVPLUS("
                   << config.ansi_c.pointer_width
                   << ", P.offset, ";
      convert_cvc_expr(index);
      cvc_prop.out << "))";
    }
  }
  else if(expr.id()=="member")
  {
    if(expr.operands().size()!=1)
      throw "member takes one operand";

    const exprt &struct_op=expr.op0();

    cvc_prop.out << "(LET P: ";
    cvc_prop.out << cvc_pointer_type();
    cvc_prop.out << " = ";
    
    convert_address_of_rec(struct_op);

    const irep_idt &component_name=
      to_member_expr(expr).get_component_name();
      
    mp_integer offset=member_offset(ns,
      to_struct_type(struct_op.type()),
      component_name);
    
    typet index_type("unsignedbv");
    index_type.set("width", config.ansi_c.pointer_width);

    exprt index=from_integer(offset, index_type);

    cvc_prop.out << " IN P WITH .offset:=BVPLUS("
                 << config.ansi_c.pointer_width
                 << ", P.offset, ";
    convert_cvc_expr(index);
    cvc_prop.out << "))";
  }
  else
    throw "don't know how to take address of: "+expr.id_string();
}

/*******************************************************************\

Function: cvc_convt::convert_rest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt cvc_convt::convert_rest(const exprt &expr)
{
  //cvc_prop.out << "%% E: " << expr << std::endl;

  literalt l=prop.new_variable();
  
  find_symbols(expr);

  cvc_prop.out << "ASSERT " << cvc_prop.cvc_literal(l) << " <=> (";
  convert_cvc_expr(expr);
  cvc_prop.out << ");" << std::endl << std::endl;

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
      cvc_prop.out << ch;
    else if(ch==':')
    {
      std::string::const_iterator next_it(it);
      next_it++;
      if(next_it!=identifier.end() && *next_it==':')
      {
        cvc_prop.out << "__";
        it=next_it;
      }
      else
      {
        cvc_prop.out << '_';
        cvc_prop.out << int(ch);
        cvc_prop.out << '_';
      }
    }
    else
    {
      cvc_prop.out << '_';
      cvc_prop.out << int(ch);
      cvc_prop.out << '_';
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
  if(expr.type().id()=="bool")
  {
    if(expr.is_true())
      cvc_prop.out << "0bin1";
    else if(expr.is_false())
      cvc_prop.out << "0bin0";
    else
    {
      cvc_prop.out << "IF ";
      convert_cvc_expr(expr);
      cvc_prop.out << " THEN 0bin1 ELSE 0bin0 ENDIF";
    }
  }
  else
    convert_cvc_expr(expr);
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

Function: cvc_convt::convert_cvc_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_cvc_expr(const exprt &expr)
{
  if(expr.id()=="symbol")
  {
    convert_identifier(expr.get_string("identifier"));
  }
  else if(expr.id()=="nondet_symbol")
  {
    convert_identifier("nondet$"+expr.get_string("identifier"));
  }
  else if(expr.id()=="typecast")
  {
    assert(expr.operands().size()==1);
    const exprt &op=expr.op0();
    
    if(expr.type().id()=="bool")
    {
      if(op.type().id()=="signedbv" ||
         op.type().id()=="unsignedbv" ||
         op.type().id()=="pointer")
      {
        convert_cvc_expr(op);
        cvc_prop.out << "/=";
        convert_cvc_expr(gen_zero(op.type()));
      }
      else
      {
        throw "TODO typecast1 "+op.type().id_string()+" -> bool";
      }
    }
    else if(expr.type().id()=="signedbv" ||
            expr.type().id()=="unsignedbv")
    {
      unsigned to_width=atoi(expr.type().get("width").c_str());
      
      if(op.type().id()=="signedbv")
      {
        unsigned from_width=atoi(op.type().get("width").c_str());
        
        if(from_width==to_width)
          convert_cvc_expr(op);
        else if(from_width<to_width)
        {
          cvc_prop.out << "SX(";
          convert_cvc_expr(op);
          cvc_prop.out << ", " << to_width << ")";
        }
        else
        {
          cvc_prop.out << "(";
          convert_cvc_expr(op);
          cvc_prop.out << ")[" << (to_width-1) << ":0]";
        }
      }
      else if(op.type().id()=="unsignedbv")
      {
        unsigned from_width=atoi(op.type().get("width").c_str());
        
        if(from_width==to_width)
          convert_cvc_expr(op);
        else if(from_width<to_width)
        {
          cvc_prop.out << "(0bin";

          for(unsigned i=from_width; i<to_width; i++)
            cvc_prop.out << "0";

          cvc_prop.out << " @ ";
            
          cvc_prop.out << "(";
          convert_cvc_expr(op);
          cvc_prop.out << "))";
        }
        else
        {
          cvc_prop.out << "(";
          convert_cvc_expr(op);
          cvc_prop.out << ")[" << (to_width-1) << ":0]";
        }
      }
      else if(op.type().id()=="bool")
      {
        if(to_width>1)
        {
          cvc_prop.out << "(0bin";

          for(unsigned i=1; i<to_width; i++)
            cvc_prop.out << "0";

          cvc_prop.out << " @ ";
          
          cvc_prop.out << "IF ";
          convert_cvc_expr(op);
          cvc_prop.out << " THEN 0bin1 ELSE 0bin0 ENDIF)";
        }
        else
        {
          cvc_prop.out << "IF ";
          convert_cvc_expr(op);
          cvc_prop.out << " THEN 0bin1 ELSE 0bin0 ENDIF";
        }
      }
      else
      {
        throw "TODO typecast2 "+op.type().id_string()+
              " -> "+expr.type().id_string();
      }
    }
    else if(expr.type().id()=="pointer")
    {
      if(op.type().id()=="pointer")
      {
        convert_cvc_expr(op);
      }
      else
        throw "TODO typecast3 "+op.type().id_string()+" -> pointer";
    }
    else
      throw "TODO typecast4 ? -> "+expr.type().id_string();
  }
  else if(expr.id()=="struct")
  {
    cvc_prop.out << "(# ";
    
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
      if(i!=0) cvc_prop.out << ", ";
      cvc_prop.out << it->get("name");
      cvc_prop.out << ":=";
      convert_cvc_expr(expr.operands()[i]);
    }
    
    cvc_prop.out << " #)";
  }
  else if(expr.id()=="constant")
  {
    if(expr.type().id()=="unsignedbv" ||
       expr.type().id()=="signedbv" ||
       expr.type().id()=="bv")
    {
      const irep_idt &value=expr.get("value");
      
      if(value.size()==8 ||
         value.size()==16 ||
         value.size()==32 ||
         value.size()==64)
      {
        unsigned w=value.size()/4;
      
        mp_integer i=binary2integer(id2string(value), false);
        std::string hex=integer2string(i, 16);
        
        while(hex.size()<w) hex="0"+hex;
        
        cvc_prop.out << "0hex" << hex;
      }
      else
      {
        cvc_prop.out << "0bin" << value;
      }
    }
    else if(expr.type().id()=="pointer")
    {
      const irep_idt &value=expr.get("value");
      
      if(value=="NULL")
      {
        cvc_prop.out << "(# object:="
                     << pointer_logic.get_null_object()
                     << ", offset:="
                     << bin_zero(config.ansi_c.pointer_width) << " #)";
      }
      else
        throw "unknown pointer constant: "+id2string(value);
    }
    else if(expr.type().id()=="bool")
    {
      if(expr.is_true())
        cvc_prop.out << "TRUE";
      else if(expr.is_false())
        cvc_prop.out << "FALSE";
      else
        throw "unknown boolean constant";
    }
    else if(expr.type().id()=="array")
    {
      cvc_prop.out << "ARRAY (i: " << array_index_type() << "):";
      
      assert(expr.operands().size()!=0);
      
      unsigned i=0;
      forall_operands(it, expr)
      {
        if(i==0)
          cvc_prop.out << "\n  IF ";
        else
          cvc_prop.out << "\n  ELSIF ";

        cvc_prop.out << "i=" << array_index(i) << " THEN ";
        convert_array_value(*it);
        i++;
      }
      
      cvc_prop.out << "\n  ELSE ";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << "\n  ENDIF";
    }
    else if(expr.type().id()=="integer" ||
            expr.type().id()=="natural" ||
            expr.type().id()=="range")
    {
      cvc_prop.out << expr.get("value");
    }
    else
    {
      std::cerr << expr.pretty() << std::endl;
      throw "unknown constant: "+expr.type().id_string();
    }
  }
  else if(expr.id()=="concatenation" || 
          expr.id()=="bitand" ||
          expr.id()=="bitor")
  {
    cvc_prop.out << "(";

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
      {
        if(expr.id()=="concatenation")
          cvc_prop.out << " @ ";
        else if(expr.id()=="bitand")
          cvc_prop.out << " & ";
        else if(expr.id()=="bitor")
          cvc_prop.out << " | ";
      }

      convert_as_bv(*it);
    }

    cvc_prop.out << ")";
  }
  else if(expr.id()=="bitxor")
  {
    assert(!expr.operands().empty());
  
    if(expr.operands().size()==1)
    {
      convert_cvc_expr(expr.op0());
    }
    else if(expr.operands().size()==2)
    {
      cvc_prop.out << "BVXOR(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else
    {
      assert(expr.operands().size()>=3);
      
      exprt tmp(expr);
      tmp.operands().resize(tmp.operands().size()-1);

      cvc_prop.out << "BVXOR(";
      convert_cvc_expr(tmp);
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.operands().back());
      cvc_prop.out << ")";
    }
  }
  else if(expr.id()=="bitnand")
  {
    assert(expr.operands().size()==2);

    cvc_prop.out << "BVNAND(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ", ";
    convert_cvc_expr(expr.op1());
    cvc_prop.out << ")";
  }
  else if(expr.id()=="bitnot")
  {
    assert(expr.operands().size()==1);
    cvc_prop.out << "~(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ")";
  }
  else if(expr.id()=="unary-")
  {
    assert(expr.operands().size()==1);
    if(expr.type().id()=="unsignedbv" ||
       expr.type().id()=="signedbv")
    {
      cvc_prop.out << "BVUMINUS(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ")";
    }
    else
      throw "unsupported type for unary-: "+expr.type().id_string();
  }
  else if(expr.id()=="if")
  {
    assert(expr.operands().size()==3);
    cvc_prop.out << "IF ";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << " THEN ";
    convert_cvc_expr(expr.op1());
    cvc_prop.out << " ELSE ";
    convert_cvc_expr(expr.op2());
    cvc_prop.out << " ENDIF";
  }
  else if(expr.id()=="and" ||
          expr.id()=="or" ||
          expr.id()=="xor")
  {
    assert(expr.type().id()=="bool");
    
    if(expr.operands().size()>=2)
    {
      forall_operands(it, expr)
      {
        if(it!=expr.operands().begin())
        {
          if(expr.id()=="and")
            cvc_prop.out << " AND ";
          else if(expr.id()=="or")
            cvc_prop.out << " OR ";
          else if(expr.id()=="xor")
            cvc_prop.out << " XOR ";
        }
        
        cvc_prop.out << "(";
        convert_cvc_expr(*it);
        cvc_prop.out << ")";
      }
    }
    else if(expr.operands().size()==1)
    {
      convert_cvc_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()=="not")
  {
    assert(expr.operands().size()==1);
    cvc_prop.out << "NOT (";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ")";
  }
  else if(expr.id()=="=" ||
          expr.id()=="notequal")
  {
    assert(expr.operands().size()==2);
    assert(expr.op0().type()==expr.op1().type());

    if(expr.op0().type().id()=="bool")
    {
      if(expr.id()=="notequal") cvc_prop.out << "NOT (";
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ") <=> (";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
      if(expr.id()=="notequal") cvc_prop.out << ")";
    }
    else
    {
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ")";
      cvc_prop.out << (expr.id()=="="?"=":"/=");
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
  }
  else if(expr.id()=="<=" ||
          expr.id()=="<" ||
          expr.id()==">=" ||
          expr.id()==">")
  {
    assert(expr.operands().size()==2);
    
    const typet &op_type=expr.op0().type();

    if(op_type.id()=="unsignedbv")
    {
      if(expr.id()=="<=")
        cvc_prop.out << "BVLE";
      else if(expr.id()=="<")
        cvc_prop.out << "BVLT";
      else if(expr.id()==">=")
        cvc_prop.out << "BVGE";
      else if(expr.id()==">")
        cvc_prop.out << "BVGT";
      
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else if(op_type.id()=="signedbv")
    {
      if(expr.id()=="<=")
        cvc_prop.out << "SBVLE";
      else if(expr.id()=="<")
        cvc_prop.out << "SBVLT";
      else if(expr.id()==">=")
        cvc_prop.out << "SBVGE";
      else if(expr.id()==">")
        cvc_prop.out << "SBVGT";
      
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.type().id_string();
  }
  else if(expr.id()=="+")
  {
    if(expr.operands().size()>=2)
    {
      if(expr.type().id()=="unsignedbv" ||
         expr.type().id()=="signedbv")
      {
        cvc_prop.out << "BVPLUS(" << expr.type().get("width");

        forall_operands(it, expr)
        {
          cvc_prop.out << ", ";
          convert_cvc_expr(*it);
        }
          
        cvc_prop.out << ")";
      }
      else if(expr.type().id()=="pointer")
      {
        if(expr.operands().size()!=2)
          throw "pointer arithmetic with more than two operands";
        
        const exprt *p, *i;
        
        if(expr.op0().type().id()=="pointer")
        {
          p=&expr.op0();
          i=&expr.op1();
        }
        else if(expr.op1().type().id()=="pointer")
        {
          p=&expr.op1();
          i=&expr.op0();
        }
        else
          throw "unexpected mixture in pointer arithmetic";
        
        cvc_prop.out << "(LET P: " << cvc_pointer_type() << " = ";
        convert_cvc_expr(*p);
        cvc_prop.out << " IN P WITH .offset:=BVPLUS("
                     << config.ansi_c.pointer_width
                     << ", P.offset, ";
        convert_cvc_expr(*i);
        cvc_prop.out << "))";
      }
      else
        throw "unsupported type for +: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_cvc_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()=="-")
  {
    if(expr.operands().size()==2)
    {
      if(expr.type().id()=="unsignedbv" ||
         expr.type().id()=="signedbv")
      {
        cvc_prop.out << "BVSUB(" << expr.type().get("width") << ", ";
        convert_cvc_expr(expr.op0());
        cvc_prop.out << ", ";
        convert_cvc_expr(expr.op1());
        cvc_prop.out << ")";
      }
      else
        throw "unsupported type for -: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_cvc_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()=="/")
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()=="unsignedbv" ||
       expr.type().id()=="signedbv")
    {
      if(expr.type().id()=="unsignedbv")
        cvc_prop.out << "BVDIV";
      else
        cvc_prop.out << "SBVDIV";

      cvc_prop.out << "(" << expr.type().get("width") << ", ";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else
      throw "unsupported type for /: "+expr.type().id_string();
  }
  else if(expr.id()=="mod")
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()=="unsignedbv" ||
       expr.type().id()=="signedbv")
    {
      if(expr.type().id()=="unsignedbv")
        cvc_prop.out << "BVMOD";
      else
        cvc_prop.out << "SBVMOD";

      cvc_prop.out << "(" << expr.type().get("width") << ", ";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else
      throw "unsupported type for mod: "+expr.type().id_string();
  }
  else if(expr.id()=="*")
  {
    if(expr.operands().size()==2)
    {
      if(expr.type().id()=="unsignedbv" ||
         expr.type().id()=="signedbv")
      {
        cvc_prop.out << "BVMULT(" << expr.type().get("width") << ", ";
        convert_cvc_expr(expr.op0());
        cvc_prop.out << ", ";
        convert_cvc_expr(expr.op1());
        cvc_prop.out << ")";
      }
      else
        throw "unsupported type for *: "+expr.type().id_string();
    }
    else if(expr.operands().size()==1)
    {
      convert_cvc_expr(expr.op0());
    }
    else
      assert(false);
  }
  else if(expr.id()=="address_of" ||
          expr.id()=="implicit_address_of" ||
          expr.id()=="reference_to")
  {
    assert(expr.operands().size()==1);
    assert(expr.type().id()=="pointer");
    convert_address_of_rec(expr.op0());
  }
  else if(expr.id()=="array_of")
  {
    assert(expr.type().id()=="array");
    assert(expr.operands().size()==1);
    cvc_prop.out << "(ARRAY (i: " << array_index_type() << "): ";
    convert_array_value(expr.op0());
    cvc_prop.out << ")";
  }
  else if(expr.id()=="index")
  {
    assert(expr.operands().size()==2);
    cvc_prop.out << "(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ")[";
    convert_array_index(expr.op1());
    cvc_prop.out << "]";
  }
  else if(expr.id()=="ashr" ||
          expr.id()=="lshr" ||
          expr.id()=="shl")
  {
    assert(expr.operands().size()==2);

    if(expr.type().id()=="unsignedbv" ||
       expr.type().id()=="signedbv")
    {
      if(expr.id()=="ashr")
        cvc_prop.out << "BVASHR";
      else if(expr.id()=="lshr")
        cvc_prop.out << "BVLSHR";
      else if(expr.id()=="shl")
        cvc_prop.out << "BVSHL";
      else
        assert(false);

      cvc_prop.out << "(" << expr.type().get("width") << ", ";
      convert_cvc_expr(expr.op0());
      cvc_prop.out << ", ";
      convert_cvc_expr(expr.op1());
      cvc_prop.out << ")";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.type().id_string();
  }
  else if(expr.id()=="with")
  {
    assert(expr.operands().size()>=1);
    cvc_prop.out << "(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ")";
  
    for(unsigned i=1; i<expr.operands().size(); i+=2)
    {
      assert((i+1)<expr.operands().size());
      const exprt &index=expr.operands()[i];
      const exprt &value=expr.operands()[i+1];

      if(expr.type().id()=="struct")
      {
        cvc_prop.out << " WITH ." << index.get("component_name");
        cvc_prop.out << ":=(";
        convert_array_value(value);
        cvc_prop.out << ")";
      }
      else if(expr.type().id()=="union")
      {
        cvc_prop.out << " WITH ." << index.get("component_name");
        cvc_prop.out << ":=(";
        convert_array_value(value);
        cvc_prop.out << ")";
      }
      else if(expr.type().id()=="array")
      {
        cvc_prop.out << " WITH [";
        convert_array_index(index);
        cvc_prop.out << "]:=(";
        convert_array_value(value);
        cvc_prop.out << ")";
      }
      else
        throw "with expects struct or array type, but got "+expr.type().id_string();
    }
  }
  else if(expr.id()=="member")
  {
    assert(expr.operands().size()==1);
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ".";
    cvc_prop.out << expr.get("component_name");
  }
  else if(expr.id()=="pointer_offset")
  {
    assert(expr.operands().size()==1);
    cvc_prop.out << "(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ").offset";
  }
  #if 0
  else if(expr.id()=="pointer_object")
  {
    assert(expr.operands().size()==1);
    cvc_prop.out << "(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ").object";
    // TODO, this has the wrong type
  }
  #endif
  else if(expr.id()=="same-object")
  {
    assert(expr.operands().size()==2);
    cvc_prop.out << "(";
    convert_cvc_expr(expr.op0());
    cvc_prop.out << ").object=(";
    convert_cvc_expr(expr.op1());
    cvc_prop.out << ").object";
  }
  else if(expr.id()==ID_string_constant)
  {
    convert_cvc_expr(to_string_constant(expr).to_array_expr());
  }
  else if(expr.id()=="extractbit")
  {
    assert(expr.operands().size()==2);

    if(expr.op0().type().id()=="unsignedbv" ||
       expr.op0().type().id()=="signedbv")
    {
      cvc_prop.out << "(";
      convert_cvc_expr(expr.op0());
      
      mp_integer i;
      if(to_integer(expr.op1(), i))
        throw "extractbit takes constant as second parameter";
        
      cvc_prop.out << "[" << i << ":" << i << "]=0bin1)";
    }
    else
      throw "unsupported type for "+expr.id_string()+": "+expr.op0().type().id_string();
  }
  else if(expr.id()=="replication")
  {
    assert(expr.operands().size()==2);
  
    mp_integer times;
    if(to_integer(expr.op0(), times))
      throw "replication takes constant as first parameter";
    
    cvc_prop.out << "(LET v: BITVECTOR(1) = ";

    convert_cvc_expr(expr.op1());

    cvc_prop.out << " IN ";

    for(mp_integer i=0; i<times; ++i)
    {
      if(i!=0) cvc_prop.out << "@";
      cvc_prop.out << "v";
    }
    
    cvc_prop.out << ")";
  }
  else
    throw "convert_cvc_expr: "+expr.id_string()+" is unsupported";
}

/*******************************************************************\

Function: cvc_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::set_to(const exprt &expr, bool value)
{
  if(value && expr.id()=="and")
  {
    forall_operands(it, expr)
      set_to(*it, true);
    return;
  }
  
  if(value && expr.is_true())
    return;

  cvc_prop.out << "%% set_to " << (value?"true":"false") << std::endl;

  if(expr.id()=="=" && value)
  {
    assert(expr.operands().size()==2);
    
    if(expr.op0().id()=="symbol")
    {
      const irep_idt &identifier=expr.op0().get("identifier");
      
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
          cvc_prop.out << ": ";
          convert_cvc_type(expr.op0().type());
          cvc_prop.out << " = ";
          convert_cvc_expr(expr.op1());
        
          cvc_prop.out << ";" << std::endl << std::endl;
          return;
        }
      }
    }
  }
  
  find_symbols(expr);

  cvc_prop.out << "ASSERT ";

  if(!value)
    cvc_prop.out << "NOT (";
    
  convert_cvc_expr(expr);

  if(!value)
    cvc_prop.out << ")";
    
  cvc_prop.out << ";" << std::endl << std::endl;
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
    
  if(expr.id()=="symbol")
  {
    if(expr.type().id()=="code")
      return;

    const irep_idt &identifier=expr.get("identifier");

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      convert_identifier(id2string(identifier));
      cvc_prop.out << ": ";
      convert_cvc_type(expr.type());
      cvc_prop.out << ";" << std::endl;
    }
  }  
  else if(expr.id()=="nondet_symbol")
  {
    if(expr.type().id()=="code")
      return;

    const irep_idt identifier="nondet$"+expr.get_string("identifier");

    identifiert &id=identifier_map[identifier];

    if(id.type.is_nil())
    {
      id.type=expr.type();

      convert_identifier(id2string(identifier));
      cvc_prop.out << ": ";
      convert_cvc_type(expr.type());
      cvc_prop.out << ";" << std::endl;
    }
  }  
}

/*******************************************************************\

Function: cvc_convt::convert_cvc_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_convt::convert_cvc_type(const typet &type)
{
  if(type.id()=="array")
  {
    const array_typet &array_type=to_array_type(type);
    
    cvc_prop.out << "ARRAY " << array_index_type()
                 << " OF ";
                 
    if(array_type.subtype().id()=="bool")
      cvc_prop.out << "BITVECTOR(1)";
    else
      convert_cvc_type(array_type.subtype());
  }
  else if(type.id()=="bool")
  {
    cvc_prop.out << "BOOLEAN";
  }
  else if(type.id()=="struct" ||
          type.id()=="union")
  {
    const struct_typet &struct_type=to_struct_type(type);
  
    cvc_prop.out << "[#";
    
    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it!=components.begin()) cvc_prop.out << ",";
      cvc_prop.out << " ";
      cvc_prop.out << it->get("name");
      cvc_prop.out << ": ";
      convert_cvc_type(it->type());
    }
    
    cvc_prop.out << " #]";
  }
  else if(type.id()=="pointer" ||
          type.id()=="reference")
  {
    cvc_prop.out << cvc_pointer_type();
  }
  else if(type.id()=="integer")
  {
    cvc_prop.out << "INT";
  }
  else if(type.id()=="signedbv")
  {
    unsigned width=to_signedbv_type(type).get_width();
      
    if(width==0)
      throw "zero-width vector type: "+type.id_string();
  
    cvc_prop.out << "BITVECTOR(" << width << ")";
  }
  else if(type.id()=="unsignedbv")
  {
    unsigned width=to_unsignedbv_type(type).get_width();
      
    if(width==0)
      throw "zero-width vector type: "+type.id_string();
  
    cvc_prop.out << "BITVECTOR(" << width << ")";
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
  if(type.id()=="array")
  {
    const array_typet &array_type=to_array_type(type);
    find_symbols(array_type.size());
  }
  else if(type.id()=="struct" ||
          type.id()=="union")
  {
  }
}
