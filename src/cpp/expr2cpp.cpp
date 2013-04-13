/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <cassert>

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/hash_cont.h>

#include <ansi-c/expr2c_class.h>

#include "expr2cpp.h"

class expr2cppt:public expr2ct
{
public:
  expr2cppt(const namespacet &_ns):expr2ct(_ns) { }

  virtual std::string convert(const exprt &src)
  {
    return expr2ct::convert(src);
  }

  virtual std::string convert(const typet &src)
  {
    return expr2ct::convert(src);
  }

protected:
  virtual std::string convert(const exprt &src, unsigned &precedence);
  virtual std::string convert_cpp_this(const exprt &src, unsigned precedence);
  virtual std::string convert_cpp_new(const exprt &src, unsigned precedence);
  virtual std::string convert_extractbit(const exprt &src, unsigned precedence);
  virtual std::string convert_extractbits(const exprt &src, unsigned precedence);
  virtual std::string convert_code_cpp_delete(const exprt &src, unsigned precedence);
  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  virtual std::string convert_code(const codet &src, unsigned indent);
  virtual std::string convert_constant(const exprt &src, unsigned &precedence);

  virtual std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator);

  typedef hash_set_cont<std::string, string_hash> id_sett;
};

/*******************************************************************\

Function: expr2cppt::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_struct(
  const exprt &src,
  unsigned &precedence)
{
  const typet &full_type=ns.follow(src.type());

  if(full_type.id()!=ID_struct)
    return convert_norep(src, precedence);

  const struct_typet &struct_type=to_struct_type(full_type);

  std::string dest="{ ";

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()==src.operands().size());

  exprt::operandst::const_iterator o_it=src.operands().begin();

  bool first=true;
  unsigned last_size=0;

  for(struct_typet::componentst::const_iterator
      c_it=components.begin();
      c_it!=components.end();
      c_it++)
  {
    if(c_it->type().id()==ID_code)
    {
    }
    else
    {
      std::string tmp=convert(*o_it);
      std::string sep;

      if(first)
        first=false;
      else
      {
        if(last_size+40<dest.size())
        {
          sep=",\n    ";
          last_size=dest.size();
        }
        else
          sep=", ";
      }

      dest+=sep;
      dest+=".";
      dest+=c_it->get_string(ID_pretty_name);
      dest+="=";
      dest+=tmp;
    }

    o_it++;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2cppt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_constant(
  const exprt &src,
  unsigned &precedence)
{
  if(src.type().id()==ID_bool)
  {
    // C++ has built-in Boolean constants, in contrast to C
    if(src.is_true())
      return "true";
    else if(src.is_false())
      return "false";
  }

  return expr2ct::convert_constant(src, precedence);
}

/*******************************************************************\

Function: expr2cppt::convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_rec(
  const typet &src,
  const c_qualifierst &qualifiers,
  const std::string &declarator)
{
  c_qualifierst new_qualifiers(qualifiers);
  new_qualifiers.read(src);
  
  const std::string d=
    declarator==""?declarator:(" "+declarator);
    
  const std::string q=
    new_qualifiers.as_string();

  if(is_reference(src))
  {
    return q+convert(src.subtype())+" &"+d;
  }
  else if(is_rvalue_reference(src))
  {
    return q+convert(src.subtype())+" &&"+d;
  }
  else if(src.get(ID_C_c_type)!=irep_idt())
  {
    const irep_idt c_type=src.get(ID_C_c_type);

    if(c_type==ID_signed_char)
      return q+"signed char"+d;
    else if(c_type==ID_unsigned_char)
      return q+"unsigned char"+d;
    else if(c_type==ID_char)
      return q+"char"+d;
    else if(c_type==ID_signed_short_int)
      return q+"short"+d;
    else if(c_type==ID_unsigned_short_int)
      return q+"unsigned short"+d;
    else if(c_type==ID_signed_int)
      return q+"int"+d;
    else if(c_type==ID_unsigned_int)
      return q+"unsigned"+d;
    else if(c_type==ID_signed_long_int)
      return q+"long"+d;
    else if(c_type==ID_unsigned_long_int)
      return q+"unsigned long"+d;
    else if(c_type==ID_signed_long_long_int)
      return q+"long long"+d;
    else if(c_type==ID_unsigned_long_long_int)
      return q+"unsigned long long"+d;
    else if(c_type==ID_wchar_t)
      return q+"wchar_t"+d;
    else if(c_type==ID_float)
      return q+"float"+d;
    else if(c_type==ID_double)
      return q+"double"+d;
    else if(c_type==ID_long_double)
      return q+"long double"+d;
    else if(c_type==ID_bool)
      return q+"bool"+d;
    else
      return expr2ct::convert_rec(src, qualifiers, declarator);
  }
  else if(src.id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_type(src).get_identifier();

    const symbolt &symbol=ns.lookup(identifier);

    if(symbol.type.id()==ID_struct ||
       symbol.type.id()==ID_incomplete_struct)
    {
      std::string dest=q;
      
      if(symbol.type.get_bool(ID_C_class))
        dest+="class";
      else if(symbol.type.get_bool(ID_C_interface))
        dest+="__interface"; // MS-specific
      else
        dest+="struct";

      if(symbol.pretty_name!=irep_idt())
        dest+=" "+id2string(symbol.pretty_name);

      dest+=d;

      return dest;
    }
    else if(symbol.type.id()==ID_c_enum)
    {
      std::string dest=q;

      dest+="enum";

      if(symbol.pretty_name!=irep_idt())
        dest+=" "+id2string(symbol.pretty_name);

      dest+=d;

      return dest;
    }
    else
      return expr2ct::convert_rec(src, qualifiers, declarator);
  }
  else if(src.id()==ID_struct ||
          src.id()==ID_incomplete_struct)
  {
    std::string dest=q;

    if(src.get_bool(ID_C_class))
      dest+="class";
    else if(src.get_bool(ID_C_interface))
      dest+="__interface"; // MS-specific
    else
      dest+="struct";

    dest+=d;

    return dest;
  }
  else if(src.id()==ID_constructor)
  {
    return "constructor ";
  }
  else if(src.id()==ID_destructor)
  {
    return "destructor ";
  }
  else if(src.id()=="cpp-template-type")
  {
    return "typename";
  }
  else if(src.id()==ID_template)
  {
    std::string dest="template<";

    const irept::subt &arguments=src.find(ID_arguments).get_sub();

    forall_irep(it, arguments)
    {
      if(it!=arguments.begin()) dest+=", ";

      const exprt &argument=(const exprt &)*it;

      if(argument.id()==ID_symbol)
      {
        dest+=convert(argument.type())+" ";
        dest+=convert(argument);
      }
      else if(argument.id()==ID_type)
        dest+=convert(argument.type());
      else
        dest+=argument.to_string();
    }

    dest+="> "+convert(src.subtype());
    return dest;
  }
  else if(src.id()==ID_pointer &&
          src.find("to-member").is_not_nil())
  {
    typet tmp=src;
    typet member;
    member.swap(tmp.add("to-member"));

    std::string dest = "(" + convert_rec(member, c_qualifierst(), "") + ":: *)";

    if(src.subtype().id()==ID_code)
    {
      const code_typet& code_type = to_code_type(src.subtype());
      const typet& return_type = code_type.return_type();
      dest = convert_rec(return_type, c_qualifierst(), "") +" " + dest;

      const code_typet::argumentst &args = code_type.arguments();
      dest += "(";

      if(args.size() > 0)
        dest+=convert_rec(args[0].type(), c_qualifierst(), "");

      for(unsigned i = 1; i < args.size();i++)
        dest += ", " +convert_rec(args[i].type(), c_qualifierst(), "");

      dest += ")";
      dest+=d;
    }
    else
      dest=convert_rec(src.subtype(), c_qualifierst(), "")+" "+dest+d;

    return dest;
  }
  else if(src.id()==ID_verilogbv)
    return "sc_lv["+id2string(src.get(ID_width))+"]"+d;
  else if(src.id()==ID_unassigned)
    return "?";
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);

    // C doesn't really have syntax for function types,
    // so we use C++11 trailing return types!
  
    std::string dest="auto ";

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
    
    const typet &return_type=code_type.return_type();
    dest+=" -> "+convert(return_type);

    return dest;
  }
  else
    return expr2ct::convert_rec(src, qualifiers, declarator);
}

/*******************************************************************\

Function: expr2cppt::convert_cpp_this

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_cpp_this(
  const exprt &src,
  unsigned precedence)
{
  return "this";
}

/*******************************************************************\

Function: expr2cppt::convert_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_cpp_new(
  const exprt &src,
  unsigned precedence)
{
  std::string dest;

  if(src.get(ID_statement)==ID_cpp_new_array)
  {
    dest="new";

    std::string tmp_size=
      convert(static_cast<const exprt &>(src.find(ID_size)));

    dest+=" ";
    dest+=convert(src.type().subtype());
    dest+="[";
    dest+=tmp_size;
    dest+="]";
  }
  else
    dest="new "+convert(src.type().subtype());

  return dest;
}

/*******************************************************************\

Function: expr2cppt::convert_code_cpp_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_code_cpp_delete(
  const exprt &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"delete ";

  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string tmp=convert(src.op0());

  dest+=tmp+";\n";

  return dest;
}

/*******************************************************************\

Function: expr2cppt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert(
  const exprt &src,
  unsigned &precedence)
{
  if(src.id()=="cpp-this")
    return convert_cpp_this(src, precedence=15);
  if(src.id()==ID_extractbit)
    return convert_extractbit(src, precedence=15);
  else if(src.id()==ID_extractbits)
    return convert_extractbits(src, precedence=15);
  else if(src.id()==ID_sideeffect &&
          (src.get(ID_statement)==ID_cpp_new ||
           src.get(ID_statement)==ID_cpp_new_array))
    return convert_cpp_new(src, precedence=15);
  else if(src.is_constant() && src.type().id() == ID_verilogbv)
    return "'" + id2string(src.get(ID_value)) + "'";
  else if(src.id()==ID_unassigned)
    return "?";
  else if(src.id()=="pod_constructor")
    return "pod_constructor";
  else
    return expr2ct::convert(src, precedence);
}

/*******************************************************************\

Function: expr2cppt::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_code(
  const codet &src,
  unsigned indent)
{
  const irep_idt &statement=src.get(ID_statement);

  if(statement==ID_cpp_delete ||
     statement==ID_cpp_delete_array)
    return convert_code_cpp_delete(src, indent);

  if(statement==ID_cpp_new ||
     statement==ID_cpp_new_array)
    return convert_cpp_new(src,indent);

  return expr2ct::convert_code(src, indent);
}


/*******************************************************************\

Function: expr2cppt::extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_extractbit(
  const exprt &src,
  unsigned precedence)
{
  assert(src.operands().size() == 2);
  return convert(src.op0()) + "[" + convert(src.op1()) + "]";
}

/*******************************************************************\

Function: expr2cppt::extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cppt::convert_extractbits(
  const exprt &src,
  unsigned precedence)
{
  assert(src.operands().size() == 3);
  return convert(src.op0()) + ".range(" + convert(src.op1()) + ","
         + convert(src.op2()) + ")";
}

/*******************************************************************\

Function: expr2cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2cpp(const exprt &expr, const namespacet &ns)
{
  expr2cppt expr2cpp(ns);
  expr2cpp.get_shorthands(expr);
  return expr2cpp.convert(expr);
}

/*******************************************************************\

Function: type2cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2cpp(const typet &type, const namespacet &ns)
{
  expr2cppt expr2cpp(ns);
  return expr2cpp.convert(type);
}
