/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cctype>
#include <cstdio>

#include <map>
#include <set>

#include <arith_tools.h>
#include <c_misc.h>
#include <config.h>
#include <std_types.h>
#include <std_code.h>
#include <i2string.h>
#include <ieee_float.h>
#include <fixedbv.h>
#include <prefix.h>
#include <lispirep.h>
#include <lispexpr.h>
#include <symbol.h>

#include "expr2c.h"
#include "c_types.h"
#include "expr2c_class.h"

/*******************************************************************\

Function: expr2ct::id_shorthand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::id_shorthand(const exprt &expr) const
{
  const irep_idt &identifier=expr.get(ID_identifier);
  const symbolt *symbol;

  if(!ns.lookup(identifier, symbol))
    return id2string(symbol->base_name);

  std::string sh=id2string(identifier);

  std::string::size_type pos=sh.rfind("::");
  if(pos!=std::string::npos)
    sh.erase(0, pos+2);

  return sh;
}

/*******************************************************************\

Function: expr2ct::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void expr2ct::get_symbols(const exprt &expr)
{
  if(expr.id()==ID_symbol)
    symbols.insert(expr);

  forall_operands(it, expr)
    get_symbols(*it);
}

/*******************************************************************\

Function: expr2ct::get_shorthands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void expr2ct::get_shorthands(const exprt &expr)
{
  get_symbols(expr);

  for(std::set<exprt>::const_iterator it=
      symbols.begin();
      it!=symbols.end();
      it++)
  {
    std::string sh=id_shorthand(*it);

    std::pair<std::map<irep_idt, exprt>::iterator, bool> result=
      shorthands.insert(
        std::pair<irep_idt, exprt>(sh, *it));

    if(!result.second)
      if(result.first->second!=*it)
      {
        ns_collision.insert(it->get(ID_identifier));
        ns_collision.insert(result.first->second.get(ID_identifier));
      }
  }
}

/*******************************************************************\

Function: expr2ct::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert(const typet &src)
{
  return convert_rec(src, c_qualifierst());
}

/*******************************************************************\

Function: expr2ct::convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_rec(
  const typet &src,
  const c_qualifierst &qualifiers)
{
  c_qualifierst new_qualifiers(qualifiers);
  new_qualifiers.read(src);

  std::string q=new_qualifiers.as_string();

  if(src.id()==ID_bool)
  {
    return q+"_Bool";
  }
  else if(src.id()==ID_natural ||
          src.id()==ID_integer ||
          src.id()==ID_rational)
  {
    return q+src.id_string();
  }
  else if(src.id()==ID_empty)
  {
    return q+"void";
  }
  else if(src.id()==ID_complex)
  {
    // these take more or less arbitrary subtypes
    return q+"_Complex "+convert(src.subtype());
  }
  else if(src.id()==ID_floatbv)
  {
    // annotated?
    
    irep_idt c_type=src.get(ID_C_c_type);

    if(c_type==ID_double)
      return q+"double";
    else if(c_type==ID_long_double)
      return q+"long double";
    else if(c_type==ID_float)
      return q+"float";

    mp_integer width=string2integer(src.get_string(ID_width));

    if(width==config.ansi_c.single_width)
      return q+"float";
    else if(width==config.ansi_c.double_width)
      return q+"double";
  }
  else if(src.id()==ID_fixedbv)
  {
    // annotated?
    
    irep_idt c_type=src.get(ID_C_c_type);

    if(c_type==ID_double)
      return q+"double";
    else if(c_type==ID_long_double)
      return q+"long double";
    else if(c_type==ID_float)
      return q+"float";

    mp_integer width=string2integer(src.get_string(ID_width));

    if(width==config.ansi_c.single_width)
      return q+"float";
    else if(width==config.ansi_c.double_width)
      return q+"double";
  }
  else if(src.id()==ID_signedbv ||
          src.id()==ID_unsignedbv)
  {
    // annotated?
    
    irep_idt c_type=src.get(ID_C_c_type);

    if(c_type==ID_unsigned_char)
      return q+"unsigned char";
    else if(c_type==ID_signed_char)
      return q+"signed char";
    else if(c_type==ID_unsigned_short_int)
      return q+"unsigned short int";
    else if(c_type==ID_signed_short_int)
      return q+"signed short int";
    else if(c_type==ID_unsigned_int)
      return q+"unsigned int";
    else if(c_type==ID_signed_int)
      return q+"signed int";
    else if(c_type==ID_unsigned_long_int)
      return q+"unsigned long int";
    else if(c_type==ID_signed_long_int)
      return q+"signed long int";
    else if(c_type==ID_unsigned_long_long_int)
      return q+"unsigned long long int";
    else if(c_type==ID_signed_long_long_int)
      return q+"signed long long int";
    else if(c_type==ID_bool)
      return q+"_Bool";
      
    // There is also wchar_t among the above, but this isn't a C type.

    mp_integer width=string2integer(src.get_string(ID_width));

    bool is_signed=src.id()==ID_signedbv;
    std::string sign_str=is_signed?"signed ":"unsigned ";

    if(width==config.ansi_c.int_width)
    {
      if(is_signed) sign_str="";
      return q+sign_str+"int";
    }
    else if(width==config.ansi_c.long_int_width)
    {
      if(is_signed) sign_str="";
      return q+sign_str+"long int";
    }
    else if(width==config.ansi_c.char_width)
    {
      // always include sign
      return q+sign_str+"char";
    }
    else if(width==config.ansi_c.short_int_width)
    {
      if(is_signed) sign_str="";
      return q+sign_str+"short int";
    }
    else if(width==config.ansi_c.long_long_int_width)
    {
      if(is_signed) sign_str="";
      return q+sign_str+"long long int";
    }
    else
    {
      return q+sign_str+"__CPROVER_bitvector["+integer2string(width)+"]";
    }
  }
  else if(src.id()==ID_struct ||
          src.id()==ID_incomplete_struct)
  {
    std::string dest=q+"struct";

    const std::string &tag=src.get_string(ID_tag);
    if(tag!="") dest+=" "+tag;
    
    /*
    const irept &components=type.find(ID_components);

    forall_irep(it, components.get_sub())
    {
      typet &subtype=(typet &)it->find(ID_type);
      base_type(subtype, ns);
    }
    */

    return dest;
  }
  else if(src.id()==ID_union ||
          src.id()==ID_incomplete_union)
  {
    std::string dest=q+"union";

    const std::string &tag=src.get_string(ID_tag);
    if(tag!="") dest+=" "+tag;

    /*
    const irept &components=type.find(ID_components);

    forall_irep(it, components.get_sub())
    {
      typet &subtype=(typet &)it->find(ID_type);
      base_type(subtype, ns);
    }
    */

    return dest;
  }
  else if(src.id()==ID_c_enum ||
          src.id()==ID_incomplete_c_enum)
  {
    std::string result=q+"enum";
    if(src.get(ID_name)!="") result+=" "+src.get_string(ID_tag);
    return result;
  }
  else if(src.id()==ID_pointer)
  {
    const typet &subtype=ns.follow(src.subtype());
  
    if(subtype.id()==ID_code)
    {
      const typet &return_type=to_code_type(subtype).return_type();

      std::string dest=q+convert(return_type);

      // function "name"
      dest+=" (*)";

      // arguments
      dest+="(";
      const irept &arguments=subtype.find(ID_arguments);

      forall_irep(it, arguments.get_sub())
      {
        const typet &argument_type=((exprt &)*it).type();

        if(it!=arguments.get_sub().begin())
          dest+=", ";

        dest+=convert(argument_type);
      }

      if(to_code_type(subtype).has_ellipsis())
      {
        if(!arguments.get_sub().empty()) dest+=", ";
        dest+="...";
      }

      dest+=")";

      return dest;
    }
    else
    {
      std::string tmp=convert(subtype);
      tmp+=" *";
      if(q!="")
      {
        tmp+=" "+q;
        // strip training space off q
        if(tmp[tmp.size()-1]==' ')
          tmp.resize(tmp.size()-1);
      }
      return tmp;
    }
  }
  else if(src.id()==ID_array)
  {
    if(to_array_type(src).size().is_nil())
      return convert(src.subtype())+" []";

    std::string size_string=convert(to_array_type(src).size());
    return convert(src.subtype())+" ["+size_string+"]";
  }
  else if(src.id()==ID_incomplete_array)
  {
    return convert(src.subtype())+" []";
  }
  else if(src.id()==ID_symbol)
  {
    return convert_rec(ns.follow(src), new_qualifiers);
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
  
    const typet &return_type=code_type.return_type();

    std::string dest=convert(return_type)+" ";

    dest+="(";
    const code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::const_iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      if(it!=arguments.begin())
        dest+=", ";

      dest+=convert(it->type());
    }
    
    if(code_type.has_ellipsis())
    {
      if(!arguments.empty()) dest+=", ";
      dest+="...";
    }

    dest+=")";
    return dest;
  }
  else if(src.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(src);
    std::string dest="VECTOR(";
    dest+=convert(vector_type.size());
    dest+=", ";
    dest+=convert(vector_type.subtype());
    dest+=")";
    return q+dest;
  }

  {
    lispexprt lisp;
    irep2lisp(src, lisp);
    std::string dest="irep(\"";
    MetaString(dest, lisp.expr2string());
    dest+="\")";

    return dest;
  }
}

/*******************************************************************\

Function: expr2ct::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_typecast(
  const exprt &src,
  unsigned &precedence)
{
  precedence=14;

  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  // some special cases

  const typet &type=ns.follow(src.type());

  if(type.id()==ID_pointer &&
     ns.follow(type.subtype()).id()==ID_empty && // to (void *)?
     src.op0().is_zero())
    return "NULL";

  std::string dest="("+convert(type)+")";

  std::string tmp=convert(src.op0(), precedence);

  if(src.op0().id()==ID_constant ||
     src.op0().id()==ID_symbol) // better fix precedence
    dest+=tmp;
  else
    dest+='('+tmp+')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_implicit_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_implicit_address_of(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return convert(src.op0(), precedence);
}

/*******************************************************************\

Function: expr2ct::convert_trinary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_trinary(
  const exprt &src,
  const std::string &symbol1,
  const std::string &symbol2,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  const exprt::operandst &operands=src.operands();
  const exprt &op0=operands.front();
  const exprt &op1=*(++operands.begin());
  const exprt &op2=operands.back();

  unsigned p0, p1, p2;

  std::string s_op0=convert(op0, p0);
  std::string s_op1=convert(op1, p1);
  std::string s_op2=convert(op2, p2);

  std::string dest;

  if(precedence>=p0) dest+='(';
  dest+=s_op0;
  if(precedence>=p0) dest+=')';

  dest+=' ';
  dest+=symbol1;
  dest+=' ';

  if(precedence>=p1) dest+='(';
  dest+=s_op1;
  if(precedence>=p1) dest+=')';

  dest+=' ';
  dest+=symbol2;
  dest+=' ';

  if(precedence>=p2) dest+='(';
  dest+=s_op2;
  if(precedence>=p2) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_quantifier(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p0, p1;

  std::string op0=convert(src.op0(), p0);
  std::string op1=convert(src.op1(), p1);

  std::string dest=symbol+" { ";
  dest+=convert(src.op0().type());  
  dest+=" "+op0+"; ";
  dest+=op1;
  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_with(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()<3)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert(src.op0(), p0);

  std::string dest;

  if(precedence>p0) dest+='(';
  dest+=op0;
  if(precedence>p0) dest+=')';

  dest+=" WITH [";

  for(unsigned i=1; i<src.operands().size(); i+=2)
  {
    std::string op1, op2;
    unsigned p1, p2;

    if(i!=1) dest+=", ";

    if(src.operands()[i].id()==ID_member_name)
    {
      const irep_idt &component_name=
        src.operands()[i].get(ID_component_name);

      const typet &full_type=ns.follow(src.op0().type());

      const struct_union_typet &struct_union_type=
        to_struct_union_type(full_type);

      const exprt comp_expr=
        struct_union_type.get_component(component_name);
        
      assert(comp_expr.is_not_nil());
        
      op1="."+comp_expr.get_string(ID_pretty_name);
      p1=10;
    }
    else
      op1=convert(src.operands()[i], p1);

    op2=convert(src.operands()[i+1], p2);

    dest+=op1;
    dest+=":=";
    dest+=op2;
  }

  dest+="]";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_cond(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()<2)
    return convert_norep(src, precedence);

  bool condition=true;

  std::string dest="cond {\n";

  forall_operands(it, src)
  {
    unsigned p;
    std::string op=convert(*it, p);

    if(condition) dest+="  ";

    dest+=op;

    if(condition)
      dest+=": ";
    else
      dest+=";\n";

    condition=!condition;
  }

  dest+="} ";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_binary(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence,
  bool full_parentheses)
{
  if(src.operands().size()<2)
    return convert_norep(src, precedence);

  std::string dest;
  bool first=true;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      if(symbol!=", ") dest+=' ';
      dest+=symbol;
      dest+=' ';
    }

    unsigned p;
    std::string op=convert(*it, p);

    if(precedence>p || (precedence==p && full_parentheses)) dest+='(';
    dest+=op;
    if(precedence>p || (precedence==p && full_parentheses)) dest+=')';
  }

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_unary(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert(src.op0(), p);

  std::string dest=symbol;
  if(precedence>=p) dest+='(';
  dest+=op;
  if(precedence>=p) dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_pointer_object_has_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_pointer_object_has_type(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert(src.op0(), p0);

  std::string dest="POINTER_OBJECT_HAS_TYPE";
  dest+='(';
  dest+=op0;
  dest+=", ";
  dest+=convert(static_cast<const typet &>(src.find("object_type")));
  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_malloc(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert(src.op0(), p0);

  std::string dest="MALLOC";
  dest+='(';
  dest+=convert((const typet &)src.find("#type"));
  dest+=", ";
  dest+=op0;
  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_nondet(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=0)
    return convert_norep(src, precedence);

  return "NONDET("+convert(src.type())+")";
}

/*******************************************************************\

Function: expr2ct::convert_statement_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_statement_expression(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "({"+convert_code(to_code(src.op0()), 0)+"})";
}

/*******************************************************************\

Function: expr2ct::convert_prob_coin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_prob_coin(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
    return "COIN("+convert(src.op0())+")";
  else
    return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2ct::convert_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_literal(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
    return "L("+src.get_string(ID_literal)+")";
  else
    return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2ct::convert_prob_uniform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_prob_uniform(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
    return "PROB_UNIFORM("+convert(src.type())+","+convert(src.op0())+")";
  else
    return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2ct::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_function(
  const exprt &src,
  const std::string &name,
  unsigned precedence)
{
  std::string dest=name;
  dest+='(';

  forall_operands(it, src)
  {
    unsigned p;
    std::string op=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";

    dest+=op;
  }

  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_complex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_complex(
  const exprt &src,
  unsigned precedence)
{
  // ISO C11 offers:
  // double complex CMPLX(double x, double y);
  // float complex CMPLXF(float x, float y);
  // long double complex CMPLXL(long double x, long double y);
  
  const typet &subtype=
    ns.follow(ns.follow(src.type()).subtype());

  std::string name;
  
  if(subtype==double_type())
    name="CMPLX";
  else if(subtype==float_type())
    name="CMPLXF";
  else if(subtype==long_double_type())
    name="CMPLXL";
  else
    name="CMPLX"; // default, possibly wrong

  std::string dest=name;
  dest+='(';

  forall_operands(it, src)
  {
    unsigned p;
    std::string op=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";

    dest+=op;
  }

  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_array_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_array_of(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "ARRAY_OF("+convert(src.op0())+')';
}

/*******************************************************************\

Function: expr2ct::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_byte_extract(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert(src.op0(), p0);

  unsigned p1;
  std::string op1=convert(src.op1(), p1);

  std::string dest=src.id_string();
  dest+='(';
  dest+=op0;
  dest+=", ";
  dest+=op1;
  dest+=", ";
  dest+=convert(src.type());
  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_byte_update(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert(src.op0(), p0);

  unsigned p1;
  std::string op1=convert(src.op1(), p1);

  unsigned p2;
  std::string op2=convert(src.op2(), p2);

  std::string dest=src.id_string();
  dest+='(';
  dest+=op0;
  dest+=", ";
  dest+=op1;
  dest+=", ";
  dest+=op2;
  dest+=", ";
  dest+=convert(src.op2().type());
  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_unary_post

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_unary_post(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert(src.op0(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';
  dest+=symbol;

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_index(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert(src.op0(), p);

  std::string dest;
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+='[';
  dest+=convert(src.op1());
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_pointer_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_pointer_arithmetic(
  const exprt &src, unsigned &precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);
  
  std::string dest="POINTER_ARITHMETIC(";

  unsigned p;
  std::string op;
  
  op=convert(src.op0().type());
  dest+=op;
  
  dest+=", ";

  op=convert(src.op0(), p);
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';
  
  dest+=", ";

  op=convert(src.op1(), p);
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_pointer_difference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_pointer_difference(
  const exprt &src, unsigned &precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);
  
  std::string dest="POINTER_DIFFERENCE(";

  unsigned p;
  std::string op;
  
  op=convert(src.op0().type());
  dest+=op;
  
  dest+=", ";

  op=convert(src.op0(), p);
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';
  
  dest+=", ";

  op=convert(src.op1(), p);
  if(precedence>p) dest+='(';
  dest+=op;
  if(precedence>p) dest+=')';

  dest+=')';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_member(
  const member_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string dest;

  if(src.op0().id()==ID_dereference &&
     src.operands().size()==1)
  {
    std::string op=convert(src.op0().op0(), p);

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';

    dest+="->";
  }
  else
  {
    std::string op=convert(src.op0(), p);

    if(precedence>p) dest+='(';
    dest+=op;
    if(precedence>p) dest+=')';

    dest+='.';
  }

  const typet &full_type=ns.follow(src.op0().type());

  if(full_type.id()!=ID_struct &&
     full_type.id()!=ID_union)
    return convert_norep(src, precedence);

  const struct_union_typet &struct_union_type=
    to_struct_union_type(full_type);

  irep_idt component_name=src.get_component_name();
  
  if(component_name!="")
  {
    const exprt comp_expr=
      struct_union_type.get_component(component_name);

    if(comp_expr.is_nil())
      return convert_norep(src, precedence);
      
    dest+=comp_expr.get_string(ID_pretty_name);

    return dest;
  }  

  unsigned n=src.get_component_number();
  
  if(n>=struct_union_type.components().size())
    return convert_norep(src, precedence);

  const exprt comp_expr=
    struct_union_type.components()[n];
    
  dest+=comp_expr.get_string(ID_pretty_name);

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_array_member_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_array_member_value(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "[]="+convert(src.op0());
}

/*******************************************************************\

Function: expr2ct::convert_struct_member_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_struct_member_value(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "."+src.get_string(ID_name)+"="+convert(src.op0());
}

/*******************************************************************\

Function: expr2ct::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_norep(
  const exprt &src,
  unsigned &precedence)
{
  lispexprt lisp;
  irep2lisp(src, lisp);
  std::string dest="irep(\"";
  MetaString(dest, lisp.expr2string());
  dest+="\")";
  precedence=15;
  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const irep_idt &id=src.get(ID_identifier);
  std::string dest;

  if(ns_collision.find(id)==ns_collision.end())
    dest=id_shorthand(src);
  else if(src.operands().size()==1 &&
        src.op0().id()==ID_predicate_passive_symbol)
    dest=src.op0().get(ID_identifier).as_string();
  else
    dest=id2string(id);

  if(src.id()==ID_next_symbol)
    dest="NEXT("+dest+")";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_nondet_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_nondet_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "nondet_symbol("+id+")";
}

/*******************************************************************\

Function: expr2ct::convert_predicate_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_predicate_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "ps("+id+")";
}

/*******************************************************************\

Function: expr2ct::convert_predicate_next_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_predicate_next_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "pns("+id+")";
}

/*******************************************************************\

Function: expr2ct::convert_predicate_passive_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_predicate_passive_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "pps("+id+")";
}

/*******************************************************************\

Function: expr2ct::convert_quantified_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_quantified_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return id;
}

/*******************************************************************\

Function: expr2ct::convert_nondet_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_nondet_bool(
  const exprt &src,
  unsigned &precedence)
{
  return "nondet_bool()";
}

/*******************************************************************\

Function: expr2ct::convert_object_descriptor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_object_descriptor(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string result="<";

  result+=convert(src.op0());
  result+=", ";
  result+=convert(src.op1());
  result+=", ";
  
  if(src.type().is_nil())
    result+="?";
  else
    result+=convert(src.type());

  result+=">";

  return result;
}

/*******************************************************************\

Function: expr2ct::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_constant(
  const exprt &src,
  unsigned &precedence)
{
  const typet &type=ns.follow(src.type());
  const irep_idt value=src.get(ID_value);
  std::string dest;

  if(src.id()==ID_string_constant)
  {
    dest='"';
    MetaString(dest, id2string(value));
    dest+='"';
  }
  else if(type.id()==ID_integer ||
          type.id()==ID_natural ||
          type.id()==ID_rational)
    dest=id2string(value);
  else if(type.id()==ID_c_enum ||
          type.id()==ID_incomplete_c_enum)
  {
    mp_integer int_value=string2integer(id2string(value));
    mp_integer i=0;
    const irept &body=type.find(ID_body);

    forall_irep(it, body.get_sub())
    {
      if(i==int_value)
      {
        dest=it->get_string(ID_name);
        return dest;
      }

      const exprt &v=
        static_cast<const exprt &>(it->find(ID_value));
        
      if(v.is_not_nil())
        if(to_integer(v, i))
          break;

      ++i;
    }

    // failed...
    dest="enum("+id2string(value)+")";

    return dest;
  }
  else if(type.id()==ID_rational)
    return convert_norep(src, precedence);
  else if(type.id()==ID_bv)
    dest=id2string(value);
  else if(type.id()==ID_bool)
  {
    if(src.is_true())
      dest="TRUE";
    else
      dest="FALSE";
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
  {
    mp_integer int_value=binary2integer(id2string(value), type.id()==ID_signedbv);

    if(type.get(ID_C_c_type)==ID_bool)
    {
      if(int_value!=0)
        dest="TRUE";
      else
        dest="FALSE";
    }
    else
    {
      dest=integer2string(int_value);
    
      if(src.find(ID_C_c_sizeof_type).is_not_nil())
        dest+=" [["+convert(static_cast<const typet &>(src.find(ID_C_c_sizeof_type)))+"]]";
    }
  }
  else if(type.id()==ID_floatbv)
  {
    dest=ieee_floatt(to_constant_expr(src)).to_ansi_c_string();

    if(dest!="" && isdigit(dest[dest.size()-1]))
    {
      if(src.type()==float_type())
        dest+="f";
      else if(src.type()==double_type())
        dest+=""; // ANSI-C: double is default
      else if(src.type()==long_double_type())
        dest+="l";
    }
  }
  else if(type.id()==ID_fixedbv)
  {
    dest=fixedbvt(to_constant_expr(src)).to_ansi_c_string();

    if(dest!="" && isdigit(dest[dest.size()-1]))
    {
      if(src.type()==float_type())
        dest+="f";
      else if(src.type()==double_type())
        dest+="l";
    }
  }
  else if(type.id()==ID_array ||
          type.id()==ID_incomplete_array)
  {
    dest="{ ";

    forall_operands(it, src)
    {
      std::string tmp=convert(*it);

      if((it+1)!=src.operands().end())
      {
        tmp+=", ";
        if(tmp.size()>40) tmp+="\n    ";
      }

      dest+=tmp;
    }

    dest+=" }";
  }
  else if(type.id()==ID_pointer)
  {
    if(src.is_zero())
      dest="NULL";
    else
    {
      // we prefer the annotation
      if(src.operands().size()!=1)
        return convert_norep(src, precedence);

      if(src.op0().id()==ID_constant)
      {        
        const irep_idt &op_value=src.op0().get(ID_value);
    
        if(op_value=="INVALID" ||
           has_prefix(id2string(op_value), "INVALID-") ||
           op_value=="NULL+offset")
          dest=id2string(op_value);
        else
          return convert_norep(src, precedence);
      }
      else
        return convert(src.op0(), precedence);
    }
  }
  else
    return convert_norep(src, precedence);

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_struct(
  const exprt &src,
  unsigned &precedence)
{
  const typet full_type=ns.follow(src.type());

  if(full_type.id()!=ID_struct)
    return convert_norep(src, precedence);

  std::string dest="{ ";

  const irept::subt &components=
    full_type.find(ID_components).get_sub();

  assert(components.size()==src.operands().size());

  exprt::operandst::const_iterator o_it=src.operands().begin();

  bool first=true;
  bool newline=false;
  unsigned last_size=0;

  forall_irep(c_it, components)
  {
    if(o_it->type().id()==ID_code)
      continue;

    if(first)
      first=false;
    else
    {
      dest+=",";

      if(newline)
        dest+="\n    ";
      else
        dest+=" ";
    }

    std::string tmp=convert(*o_it);

    if(last_size+40<dest.size())
    {
      newline=true;
      last_size=dest.size();
    }
    else
      newline=false;

    dest+=".";
    dest+=c_it->get_string(ID_name);
    dest+="=";
    dest+=tmp;

    o_it++;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_vector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_vector(
  const exprt &src,
  unsigned &precedence)
{
  const typet full_type=ns.follow(src.type());

  if(full_type.id()!=ID_vector)
    return convert_norep(src, precedence);

  std::string dest="{ ";

  bool first=true;
  bool newline=false;
  unsigned last_size=0;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      dest+=",";

      if(newline)
        dest+="\n    ";
      else
        dest+=" ";
    }

    std::string tmp=convert(*it);

    if(last_size+40<dest.size())
    {
      newline=true;
      last_size=dest.size();
    }
    else
      newline=false;

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_union(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest="{ ";

  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  std::string tmp=convert(src.op0());

  dest+=".";
  dest+=src.get_string(ID_component_name);
  dest+="=";
  dest+=tmp;

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_array(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest;

  // we treat arrays of characters as string constants,
  // and arrays of wchar_t as wide strings
  
  const typet &subtype=ns.follow(ns.follow(src.type()).subtype());
  
  bool all_constant=true;
  
  forall_operands(it, src)
    if(!it->is_constant())
      all_constant=false;
  
  if(src.get_bool(ID_C_string_constant) &&
     all_constant &&
     (subtype==char_type() || subtype==wchar_t_type()))
  {
    bool wide=subtype==wchar_t_type();
  
    if(wide)
      dest+="L";

    dest+="\"";
    
    dest.reserve(dest.size()+1+src.operands().size());
    
    bool last_was_hex=false;
    
    forall_operands(it, src)
    {
      // these have a trailing zero
      if(it==--src.operands().end())
        break;
        
      assert(it->is_constant());
      mp_integer i;
      to_integer(*it, i);
      unsigned int ch=integer2long(i);

      if(last_was_hex)
      {
        // we use "string splicing" to avoid ambiguity
        if(isxdigit(ch))
          dest+="\" \"";
        
        last_was_hex=false;
      }
        
      switch(ch)
      {
      case '\n': dest+="\\n"; break; /* NL (0x0a) */
      case '\t': dest+="\\t"; break; /* HT (0x09) */
      case '\v': dest+="\\v"; break; /* VT (0x0b) */
      case '\b': dest+="\\b"; break; /* BS (0x08) */
      case '\r': dest+="\\r"; break; /* CR (0x0d) */
      case '\f': dest+="\\f"; break; /* FF (0x0c) */
      case '\a': dest+="\\a"; break; /* BEL (0x07) */
      case '\\': dest+="\\"; break;
      case '"': dest+="\\\""; break;
      
      default:
        if(ch>=' ' && ch!=127 && ch<0xff)
          dest+=(char)ch;
        else
        {
          char hexbuf[10];
          sprintf(hexbuf, "\\x%x", ch);
          dest+=hexbuf;
          last_was_hex=true;
        }
      }
    }

    dest+="\"";
    
    return dest;
  }

  dest="{ ";

  forall_operands(it, src)
  {
    std::string tmp;

    if(it->is_not_nil())
      tmp=convert(*it);

    if((it+1)!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40) tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_array_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_array_list(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest="{ ";

  if((src.operands().size()%2)!=0)
    return convert_norep(src, precedence);

  forall_operands(it, src)
  {
    std::string tmp1=convert(*it);

    it++;

    std::string tmp2=convert(*it);

    std::string tmp="["+tmp1+"]="+tmp2;

    if((it+1)!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40) tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_initializer_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_initializer_list(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest="{ ";

  forall_operands(it, src)
  {
    std::string tmp=convert(*it);

    if((it+1)!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40) tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_designated_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_designated_initializer(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=".";
  // TODO it->find(ID_member)
  dest+="=";
  dest+=convert(src.op0());

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_function_application

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_function_application(
  const function_application_exprt &src,
  unsigned &precedence)
{
  std::string dest;

  {
    unsigned p;
    std::string function_str=convert(src.function(), p);
    dest+=function_str;
  }

  dest+="(";

  unsigned i=0;

  forall_expr(it, src.arguments())
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(i>0) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;

    i++;
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_side_effect_expr_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_side_effect_expr_function_call(
  const side_effect_expr_function_callt &src,
  unsigned &precedence)
{
  std::string dest;

  {
    unsigned p;
    std::string function_str=convert(src.function(), p);
    dest+=function_str;
  }

  dest+="(";

  unsigned i=0;

  forall_expr(it, src.arguments())
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(i>0) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;

    i++;
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_overflow(
  const exprt &src,
  unsigned &precedence)
{
  precedence=16;

  std::string dest="overflow(\"";
  dest+=src.id().c_str()+9;
  dest+="\"";
  
  if(!src.operands().empty())
  {
    dest+=", ";
    dest+=convert(src.op0().type());
  }

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2ct::indent_str

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::indent_str(unsigned indent)
{
  std::string dest;
  for(unsigned j=0; j<indent; j++) dest+=' ';
  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_asm(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="asm(";
  if(src.operands().size()==1)
    dest+=convert(src.op0());
  dest+=");";
  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_while(
  const code_whilet &src,
  unsigned indent)
{
  if(src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="while("+convert(src.cond());

  if(src.body().is_nil())
    dest+=");";
  else
  {
    dest+=")\n";
    dest+=convert_code(src.body(), indent+2);
  }

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_dowhile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_dowhile(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);

  if(src.op1().is_nil())
    dest+="do;";
  else
  {
    dest+="do\n";
    dest+=convert_code(to_code(src.op1()), indent+2);
    dest+=indent_str(indent);
    dest+="\n";
  }

  dest+="while("+convert(src.op0())+");";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_ifthenelse(
  const code_ifthenelset &src,
  unsigned indent)
{
  if(src.operands().size()!=3 &&
     src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="if("+convert(src.cond())+")\n";

  if(src.then_case().is_nil())
  {
    dest+=indent_str(indent+2);
    dest+=";\n";
  }
  else
    dest+=convert_code(src.then_case(), indent+2);

  if(src.operands().size()==3 && !src.else_case().is_nil())
  {
    dest+=indent_str(indent);
    dest+="else\n";
    dest+=convert_code(src.else_case(), indent+2);
  }

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_return(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=0 &&
     src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="return";

  if(src.operands().size()==1)
    dest+=" "+convert(src.op0());

  dest+=";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_goto(
  const codet &src,
  unsigned indent)
{
  std:: string dest=indent_str(indent);
  dest+="goto ";
  dest+=src.get_string(ID_destination);
  dest+=";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_break

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_break(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="break";
  dest+=";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_switch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_switch(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()<1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="switch(";
  dest+=convert(src.op0());
  dest+=")\n";

  dest+=indent_str(indent);
  dest+="{\n";

  for(unsigned i=1; i<src.operands().size(); i++)
  {
    const exprt &op=src.operands()[i];

    if(op.get(ID_statement)!=ID_block)
    {
      unsigned precedence;
      dest+=convert_norep(op, precedence);
    }
    else
    {
      forall_operands(it, op)
        dest+=convert_code(to_code(*it), indent+2);
    }
  }

  dest+=indent_str(indent);
  dest+="}";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_continue

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_continue(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="continue";
  dest+=";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_decl(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1 && src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);

  {
    dest+=convert(src.op0().type());
    dest+=" ";
  }

  dest+=convert(src.op0());

  if(src.operands().size()==2)
    dest+=" = "+convert(src.op1());

  dest+=";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_for(
  const code_fort &src,
  unsigned indent)
{
  if(src.operands().size()!=4)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="for(";

  unsigned i;
  for(i=0; i<=2; i++)
  {
    if(!src.operands()[i].is_nil())
    {
      if(i!=0) dest+=" ";
      dest+=convert(src.operands()[i]);
    }

    if(i!=2) dest+=";";
  }

  if(src.body().is_nil())
    dest+=");\n";
  else
  {
    dest+=")\n";
    dest+=convert_code(src.body(), indent+2);
  }

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_block(
  const code_blockt &src,
  unsigned indent)
{
  assert(indent>=0);
  std::string dest=indent_str(indent);
  dest+="{\n";

  forall_operands(it, src)
  {
    if(it->get(ID_statement)==ID_label)
      dest+=convert_code(to_code(*it), indent);
    else
      dest+=convert_code(to_code(*it), indent+2);

    dest+="\n";
  }

  dest+=indent_str(indent);
  dest+="}";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_expression(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);

  std::string expr_str;
  if(src.operands().size()==1)
    expr_str=convert(src.op0());
  else
  {
    unsigned precedence;
    expr_str=convert_norep(src, precedence);
  }

  dest+=expr_str+";";
  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code(
  const codet &src,
  unsigned indent)
{
  const irep_idt &statement=src.get(ID_statement);

  if(statement==ID_expression)
    return convert_code_expression(src, indent);

  if(statement==ID_block)
    return convert_code_block(to_code_block(src), indent);

  if(statement==ID_switch)
    return convert_code_switch(src, indent);

  if(statement==ID_for)
    return convert_code_for(to_code_for(src), indent);

  if(statement==ID_while)
    return convert_code_while(to_code_while(src), indent);

  if(statement==ID_asm)
    return convert_code_asm(src, indent);

  if(statement==ID_skip)
    return indent_str(indent)+";";

  if(statement==ID_dowhile)
    return convert_code_dowhile(src, indent);

  if(statement==ID_ifthenelse)
    return convert_code_ifthenelse(to_code_ifthenelse(src), indent);

  if(statement==ID_return)
    return convert_code_return(src, indent);

  if(statement==ID_goto)
    return convert_code_goto(src, indent);

  if(statement==ID_printf)
    return convert_code_printf(src, indent);

  if(statement==ID_fence)
    return convert_code_fence(src, indent);

  if(statement==ID_input)
    return convert_code_input(src, indent);

  if(statement==ID_assume)
    return convert_code_assume(src, indent);

  if(statement==ID_assert)
    return convert_code_assert(src, indent);

  if(statement==ID_break)
    return convert_code_break(src, indent);

  if(statement==ID_continue)
    return convert_code_continue(src, indent);

  if(statement==ID_decl)
    return convert_code_decl(src, indent);

  if(statement==ID_assign)
    return convert_code_assign(to_code_assign(src), indent);

  if(statement==ID_init)
    return convert_code_init(src, indent);

  if(statement=="lock")
    return convert_code_lock(src, indent);

  if(statement=="unlock")
    return convert_code_unlock(src, indent);

  if(statement==ID_function_call)
    return convert_code_function_call(to_code_function_call(src), indent);

  if(statement==ID_label)
    return convert_code_label(to_code_label(src), indent);

  if(statement==ID_free)
    return convert_code_free(src, indent);

  if(statement==ID_array_set)
    return convert_code_array_set(src, indent);

  if(statement==ID_array_copy)
    return convert_code_array_copy(src, indent);

  unsigned precedence;
  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2ct::convert_code_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_assign(
  const code_assignt &src,
  unsigned indent)
{
  std::string tmp=convert_binary(src, "=", 2, true);

  std::string dest=indent_str(indent)+tmp+";";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_free

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_free(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"FREE("+convert(src.op0())+");";
}

/*******************************************************************\

Function: expr2ct::convert_code_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_init(
  const codet &src,
  unsigned indent)
{
  std::string tmp=convert_binary(src, "=", 2, true);

  return indent_str(indent)+"INIT "+tmp+";";
}

/*******************************************************************\

Function: expr2ct::convert_code_lock

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_lock(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"LOCK("+convert(src.op0())+");";
}

/*******************************************************************\

Function: expr2ct::convert_code_unlock

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_unlock(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"UNLOCK("+convert(src.op0())+");";
}

/*******************************************************************\

Function: expr2ct::convert_code_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_function_call(
  const code_function_callt &src,
  unsigned indent)
{
  if(src.operands().size()!=3)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);

  if(src.lhs().is_not_nil())
  {
    unsigned p;
    std::string lhs_str=convert(src.lhs(), p);

    // TODO: ggf. Klammern je nach p
    dest+=lhs_str;
    dest+="=";
  }

  {
    unsigned p;
    std::string function_str=convert(src.function(), p);
    dest+=function_str;
  }

  dest+="(";

  unsigned i=0;

  const exprt::operandst &arguments=src.arguments();

  forall_expr(it, arguments)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(i>0) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;

    i++;
  }

  dest+=")";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_printf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_printf(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"PRINTF(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_fence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_fence(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"FENCE(";
  
  irep_idt att[]=
    { ID_WRfence, ID_RRfence, ID_RWfence, ID_WWfence,
      ID_RRcumul, ID_RWcumul, ID_WWcumul, ID_WRcumul,
      irep_idt() };

  bool first=true;
      
  for(unsigned i=0; !att[i].empty(); i++)
  {
    if(src.get_bool(att[i]))
    {
      if(first)
        first=false;
      else
        dest+="+";

      dest+=id2string(att[i]);
    }
  }
  
  dest+=");";
  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_input(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"INPUT(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_array_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_array_set(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"ARRAY_SET(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_array_copy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_array_copy(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"ARRAY_COPY(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert(*it, p);

    if(it!=src.operands().begin()) dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_code_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_assert(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"assert("+convert(src.op0())+");";
}

/*******************************************************************\

Function: expr2ct::convert_code_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_assume(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"assume("+convert(src.op0())+");";
}

/*******************************************************************\

Function: expr2ct::convert_code_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code_label(
  const code_labelt &src,
  unsigned indent)
{
  bool first=true;
  std::string labels_string;

  {
    irep_idt label=src.get_label();
    
    if(label!=irep_idt())
    {
      if(first) { labels_string+="\n"; first=false; }
      labels_string+=indent_str(indent);
      labels_string+=name2string(label);
      labels_string+=":\n";
    }

    const exprt::operandst &case_op=src.case_op();

    forall_expr(it, case_op)
    {
      if(first) { labels_string+="\n"; first=false; }
      labels_string+=indent_str(indent);
      labels_string+="case ";
      labels_string+=convert(*it);
      labels_string+=":\n";
    }

    if(src.is_default())
    {
      if(first) { labels_string+="\n"; first=false; }
      labels_string+=indent_str(indent);
      labels_string+="default:\n";
    }
  }

  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string tmp=convert_code(src.code(), indent+2);

  return labels_string+tmp;
}

/*******************************************************************\

Function: expr2ct::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_code(const codet &src)
{
  return convert_code(src, 0);
}

/*******************************************************************\

Function: expr2ct::convert_Hoare

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_Hoare(const exprt &src)
{
  unsigned precedence;

  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  const exprt &assumption=src.op0();
  const exprt &assertion=src.op1();
  const codet &code=
    static_cast<const codet &>(src.find(ID_code));

  std::string dest="\n";
  dest+="{";

  if(!assumption.is_nil())
  {
    std::string assumption_str=convert(assumption);
    dest+=" assume(";
    dest+=assumption_str;
    dest+=");\n";
  }
  else
    dest+="\n";

  {
    std::string code_str=convert_code(code);
    dest+=code_str;
  }

  if(!assertion.is_nil())
  {
    std::string assertion_str=convert(assertion);
    dest+="    assert(";
    dest+=assertion_str;
    dest+=");\n";
  }

  dest+="}";

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_extractbit(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest=convert(src.op0(), precedence);
  dest+='[';
  dest+=convert(src.op1(), precedence);
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert_extractbits(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest=convert(src.op0(), precedence);
  dest+='[';
  dest+=convert(src.op1(), precedence);
  dest+=", ";
  dest+=convert(src.op2(), precedence);
  dest+=']';

  return dest;
}

/*******************************************************************\

Function: expr2ct::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert(
  const exprt &src,
  unsigned &precedence)
{
  precedence=16;

  if(src.id()==ID_plus)
    return convert_binary(src, "+", precedence=12, false);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()==1)
      return convert_norep(src, precedence);
    else
      return convert_binary(src, "-", precedence=12, true);
  }

  else if(src.id()==ID_unary_minus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else
      return convert_unary(src, "-", precedence=15);
  }

  else if(src.id()==ID_unary_plus)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else     
      return convert_unary(src, "+", precedence=15);
  }

  else if(src.id()=="invalid-pointer")
  {
    return convert_function(src, "INVALID-POINTER", precedence=15);
  }

  else if(src.id()=="pointer_arithmetic")
  {
    return convert_pointer_arithmetic(src, precedence=15);
  }

  else if(src.id()=="pointer_difference")
  {
    return convert_pointer_difference(src, precedence=15);
  }

  else if(src.id()=="NULL-object")
  {
    return "NULL-object";
  }

  else if(src.id()==ID_integer_address ||
          src.id()==ID_stack_object ||
          src.id()==ID_static_object)
  {
    return id2string(src.id());
  }
  
  else if(src.id()==ID_infinity)
  {
    return convert_function(src, "INFINITY", precedence=15);
  }

  else if(src.id()=="builtin-function")
  {
    return src.get_string(ID_identifier);
  }

  else if(src.id()==ID_pointer_object)
  {
    return convert_function(src, "POINTER_OBJECT", precedence=15);
  }

  else if(src.id()=="object_value")
  {
    return convert_function(src, "OBJECT_VALUE", precedence=15);
  }

  else if(src.id()=="pointer_object_has_type")
  {
    return convert_pointer_object_has_type(src, precedence=15);
  }

  else if(src.id()==ID_array_of)
  {
    return convert_array_of(src, precedence=15);
  }

  else if(src.id()==ID_pointer_offset)
  {
    return convert_function(src, "POINTER_OFFSET", precedence=15);
  }

  else if(src.id()=="pointer_base")
  {
    return convert_function(src, "POINTER_BASE", precedence=15);
  }

  else if(src.id()=="pointer_cons")
  {
    return convert_function(src, "POINTER_CONS", precedence=15);
  }

  else if(src.id()==ID_same_object)
  {
    return convert_function(src, "SAME-OBJECT", precedence=15);
  }

  else if(src.id()==ID_dynamic_object)
  {
    return convert_function(src, "DYNAMIC_OBJECT", precedence=15);
  }

  else if(src.id()=="is_zero_string")
  {
    return convert_function(src, "IS_ZERO_STRING", precedence=15);
  }

  else if(src.id()=="zero_string")
  {
    return convert_function(src, "ZERO_STRING", precedence=15);
  }

  else if(src.id()=="zero_string_length")
  {
    return convert_function(src, "ZERO_STRING_LENGTH", precedence=15);
  }

  else if(src.id()=="buffer_size")
  {
    return convert_function(src, "BUFFER_SIZE", precedence=15);
  }

  else if(src.id()==ID_pointer_offset)
  {
    return convert_function(src, "POINTER_OFFSET", precedence=15);
  }

  else if(src.id()==ID_isnan)
  {
    return convert_function(src, "isnan", precedence=15);
  }

  else if(src.id()==ID_isfinite)
  {
    return convert_function(src, "isfinite", precedence=15);
  }

  else if(src.id()==ID_isinf)
  {
    return convert_function(src, "isinf", precedence=15);
  }

  else if(src.id()==ID_isnormal)
  {
    return convert_function(src, "isnormal", precedence=15);
  }

  else if(src.id()==ID_builtin_offsetof)
  {
    return convert_function(src, "builtin_offsetof", precedence=15);
  }

  else if(src.id()==ID_gcc_builtin_va_arg)
  {
    return convert_function(src, "gcc_builtin_va_arg", precedence=15);
  }

  else if(src.id()==ID_alignof)
  {
    // C uses "_Alignof", C++ uses "alignof"
    return convert_function(src, "alignof", precedence=15);
  }

  else if(has_prefix(src.id_string(), "byte_extract"))
  {
    return convert_byte_extract(src, precedence=15);
  }

  else if(has_prefix(src.id_string(), "byte_update"))
  {
    return convert_byte_update(src, precedence=15);
  }

  else if(src.id()==ID_address_of)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else if(src.op0().id()==ID_label)
      return "&&"+src.op0().get_string(ID_identifier);
    else
      return convert_unary(src, "&", precedence=15);
  }

  else if(src.id()==ID_dereference)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else
      return convert_unary(src, "*", precedence=15);
  }

  else if(src.id()==ID_index)
    return convert_index(src, precedence=16);

  else if(src.id()==ID_member)
    return convert_member(to_member_expr(src), precedence=16);

  else if(src.id()=="array-member-value")
    return convert_array_member_value(src, precedence=16);

  else if(src.id()=="struct-member-value")
    return convert_struct_member_value(src, precedence=16);

  else if(src.id()==ID_function_application)
    return convert_function_application(to_function_application_expr(src), precedence);
    
  else if(src.id()==ID_sideeffect)
  {
    const irep_idt &statement=src.get(ID_statement);
    if(statement==ID_preincrement)
      return convert_unary(src, "++", precedence=15);
    else if(statement==ID_predecrement)
      return convert_unary(src, "--", precedence=15);
    else if(statement==ID_postincrement)
      return convert_unary_post(src, "++", precedence=16);
    else if(statement==ID_postdecrement)
      return convert_unary_post(src, "--", precedence=16);
    else if(statement==ID_assign_plus)
      return convert_binary(src, "+=", precedence=2, true);
    else if(statement==ID_assign_minus)
      return convert_binary(src, "-=", precedence=2, true);
    else if(statement==ID_assign_mult)
      return convert_binary(src, "*=", precedence=2, true);
    else if(statement==ID_assign_div)
      return convert_binary(src, "/=", precedence=2, true);
    else if(statement==ID_assign_mod)
      return convert_binary(src, "%=", precedence=2, true);
    else if(statement==ID_assign_shl)
      return convert_binary(src, "<<=", precedence=2, true);
    else if(statement==ID_assign_shr)
      return convert_binary(src, ">>=", precedence=2, true);
    else if(statement==ID_assign_bitand)
      return convert_binary(src, "&=", precedence=2, true);
    else if(statement==ID_assign_bitxor)
      return convert_binary(src, "^=", precedence=2, true);
    else if(statement==ID_assign_bitor)
      return convert_binary(src, "|=", precedence=2, true);
    else if(statement==ID_assign)
      return convert_binary(src, "=", precedence=2, true);
    else if(statement==ID_function_call)
      return convert_side_effect_expr_function_call(to_side_effect_expr_function_call(src), precedence);
    else if(statement==ID_malloc)
      return convert_malloc(src, precedence=15);
    else if(statement==ID_printf)
      return convert_function(src, "PRINTF", precedence=15);
    else if(statement==ID_nondet)
      return convert_nondet(src, precedence=15);
    else if(statement=="prob_coin")
      return convert_prob_coin(src, precedence=15);
    else if(statement=="prob_unif")
      return convert_prob_uniform(src, precedence=15);
    else if(statement==ID_literal)
      return convert_literal(src, precedence=15);
    else if(statement==ID_statement_expression)
      return convert_statement_expression(src, precedence=15);
    else if(statement==ID_gcc_builtin_va_arg_next)
      return convert_function(src, "gcc_builtin_va_arg_next", precedence=15);
    else
      return convert_norep(src, precedence);
  }

  else if(src.id()==ID_not)
    return convert_unary(src, "!", precedence=15);

  else if(src.id()==ID_bitnot)
    return convert_unary(src, "~", precedence=15);

  else if(src.id()==ID_mult)
    return convert_binary(src, "*", precedence=13, false);

  else if(src.id()==ID_div)
    return convert_binary(src, "/", precedence=13, true);

  else if(src.id()==ID_mod)
    return convert_binary(src, "%", precedence=13, true);

  else if(src.id()==ID_shl)
    return convert_binary(src, "<<", precedence=11, true);

  else if(src.id()==ID_ashr || src.id()==ID_lshr)
    return convert_binary(src, ">>", precedence=11, true);

  else if(src.id()==ID_lt || src.id()==ID_gt ||
          src.id()==ID_le || src.id()==ID_ge)
    return convert_binary(src, src.id_string(), precedence=10, true);

  else if(src.id()==ID_notequal)
    return convert_binary(src, "!=", precedence=9, true);

  else if(src.id()==ID_equal)
    return convert_binary(src, "==", precedence=9, true);

  else if(src.id()==ID_ieee_float_equal)
    return convert_function(src, "IEEE_FLOAT_EQUAL", precedence=15);

  else if(src.id()==ID_width)
    return convert_function(src, "WIDTH", precedence=15);

  else if(src.id()==ID_concatenation)
    return convert_function(src, "CONCATENATION", precedence=15);

  else if(src.id()==ID_ieee_float_notequal)
    return convert_function(src, "IEEE_FLOAT_NOTEQUAL", precedence=15);

  else if(src.id()==ID_abs)
    return convert_function(src, "abs", precedence=15);

  else if(src.id()==ID_complex_real)
    return convert_function(src, "__real__", precedence=15);

  else if(src.id()==ID_complex_imag)
    return convert_function(src, "__imag__", precedence=15);

  else if(src.id()==ID_complex)
    return convert_complex(src, precedence=15);

  else if(src.id()==ID_bitand)
    return convert_binary(src, "&", precedence=8, false);

  else if(src.id()==ID_bitxor)
    return convert_binary(src, "^", precedence=7, false);

  else if(src.id()==ID_bitor)
    return convert_binary(src, "|", precedence=6, false);

  else if(src.id()==ID_and)
    return convert_binary(src, "&&", precedence=5, false);

  else if(src.id()==ID_or)
    return convert_binary(src, "||", precedence=4, false);

  else if(src.id()==ID_xor)
    return convert_binary(src, "^", precedence=7, false);

  else if(src.id()==ID_implies)
    return convert_binary(src, "=>", precedence=3, true);

  else if(src.id()==ID_if)
    return convert_trinary(src, "?", ":", precedence=3);

  else if(src.id()==ID_forall)
    return convert_quantifier(src, "FORALL", precedence=2);

  else if(src.id()==ID_exists)
    return convert_quantifier(src, "EXISTS", precedence=2);

  else if(src.id()=="lambda")
    return convert_quantifier(src, "LAMBDA", precedence=2);

  else if(src.id()==ID_with)
    return convert_with(src, precedence=15);

  else if(src.id()==ID_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_nondet_symbol)
    return convert_nondet_symbol(src, precedence);

  else if(src.id()==ID_predicate_symbol)
    return convert_predicate_symbol(src, precedence);

  else if(src.id()==ID_predicate_next_symbol)
    return convert_predicate_next_symbol(src, precedence);

  else if(src.id()==ID_predicate_passive_symbol)
    return convert_predicate_passive_symbol(src, precedence);

  else if(src.id()=="quant_symbol")
    return convert_quantified_symbol(src, precedence);

  else if(src.id()==ID_nondet_bool)
    return convert_nondet_bool(src, precedence);

  else if(src.id()==ID_object_descriptor)
    return convert_object_descriptor(src, precedence);

  else if(src.id()=="Hoare")
    return convert_Hoare(src);

  else if(src.id()==ID_code)
    return convert_code(to_code(src));

  else if(src.id()==ID_constant)
    return convert_constant(src, precedence);

  else if(src.id()==ID_string_constant)
    return convert_constant(src, precedence);

  else if(src.id()==ID_struct)
    return convert_struct(src, precedence);

  else if(src.id()==ID_vector)
    return convert_vector(src, precedence);

  else if(src.id()==ID_union)
    return convert_union(src, precedence);

  else if(src.id()==ID_array)
    return convert_array(src, precedence);

  else if(src.id()=="array-list")
    return convert_array_list(src, precedence);

  else if(src.id()==ID_typecast)
    return convert_typecast(src, precedence);

  else if(src.id()=="implicit_address_of")
    return convert_implicit_address_of(src, precedence);

  else if(src.id()=="implicit_dereference")
    return convert_function(src, "IMPLICIT_DEREFERENCE", precedence=15);

  else if(src.id()==ID_comma)
    return convert_binary(src, ", ", precedence=1, false);

  else if(src.id()==ID_cond)
    return convert_cond(src, precedence);

  else if(src.id()==ID_overflow_unary_minus ||
      src.id()==ID_overflow_minus ||
      src.id()==ID_overflow_mult ||
      src.id()==ID_overflow_plus)
    return convert_overflow(src, precedence);

  else if(src.id()==ID_unknown)
    return "*";

  else if(src.id()==ID_invalid)
    return "#";

  else if(src.id()==ID_extractbit)
    return convert_extractbit(src, precedence);

  else if(src.id()==ID_extractbits)
    return convert_extractbits(src, precedence);

  else if(src.id()==ID_initializer_list)
    return convert_initializer_list(src, precedence=15);

  else if(src.id()==ID_designated_initializer)
    return convert_designated_initializer(src, precedence=15);

  // no C language expression for internal representation
  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2ct::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2ct::convert(const exprt &src)
{
  unsigned precedence;
  return convert(src, precedence);
}

/*******************************************************************\

Function: expr2c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2c(const exprt &expr, const namespacet &ns)
{
  std::string code;
  expr2ct expr2c(ns);
  expr2c.get_shorthands(expr);
  return expr2c.convert(expr);
}

/*******************************************************************\

Function: type2c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2c(const typet &type, const namespacet &ns)
{
  expr2ct expr2c(ns);
  //expr2c.get_shorthands(expr);
  return expr2c.convert(type);
}
