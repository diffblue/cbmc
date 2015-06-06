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

#include "java_types.h"
#include "expr2java.h"

class expr2javat:public expr2ct
{
public:
  expr2javat(const namespacet &_ns):expr2ct(_ns) { }

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
  virtual std::string convert_java_this(const exprt &src, unsigned precedence);
  virtual std::string convert_java_new(const exprt &src, unsigned precedence);
  virtual std::string convert_code_java_delete(const exprt &src, unsigned precedence);
  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  virtual std::string convert_code(const codet &src, unsigned indent);
  virtual std::string convert_constant(const constant_exprt &src, unsigned &precedence);

  virtual std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator);

  typedef hash_set_cont<std::string, string_hash> id_sett;
};

/*******************************************************************\

Function: expr2javat::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_struct(
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
  size_t last_size=0;

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
      dest+='.';
      dest+=c_it->get_string(ID_pretty_name);
      dest+='=';
      dest+=tmp;
    }

    o_it++;
  }

  dest+=" }";

  return dest;
}

/*******************************************************************\

Function: expr2javat::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_constant(
  const constant_exprt &src,
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

Function: expr2javat::convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_rec(
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

  if(src==java_int_type())
    return q+"int"+d;
  else if(src==java_long_type())
    return q+"long"+d;
  else if(src==java_short_type())
    return q+"short"+d;
  else if(src==java_byte_type())
    return q+"byte"+d;
  else if(src==java_char_type())
    return q+"char"+d;
  else if(src==java_float_type())
    return q+"float"+d;
  else if(src==java_double_type())
    return q+"double"+d;
  else if(src==java_boolean_type())
    return q+"bool"+d;
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);

    // Java doesn't really have syntax for function types,
    // so we make one up, loosley inspired by the syntax
    // of lamda expressions.
  
    std::string dest="";

    dest+='(';
    const code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(it!=parameters.begin())
        dest+=", ";

      dest+=convert(it->type());
    }
    
    if(code_type.has_ellipsis())
    {
      if(!parameters.empty()) dest+=", ";
      dest+="...";
    }

    dest+=')';
    
    const typet &return_type=code_type.return_type();
    dest+=" -> "+convert(return_type);

    return dest;
  }
  else
    return expr2ct::convert_rec(src, qualifiers, declarator);
}

/*******************************************************************\

Function: expr2javat::convert_java_this

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_java_this(
  const exprt &src,
  unsigned precedence)
{
  return "this";
}

/*******************************************************************\

Function: expr2javat::convert_java_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_java_new(
  const exprt &src,
  unsigned precedence)
{
  std::string dest;

  if(src.get(ID_statement)==ID_java_new_array)
  {
    dest="new";

    std::string tmp_size=
      convert(static_cast<const exprt &>(src.find(ID_size)));

    dest+=' ';
    dest+=convert(src.type().subtype());
    dest+='[';
    dest+=tmp_size;
    dest+=']';
  }
  else
    dest="new "+convert(src.type().subtype());

  return dest;
}

/*******************************************************************\

Function: expr2javat::convert_code_java_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_code_java_delete(
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

Function: expr2javat::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert(
  const exprt &src,
  unsigned &precedence)
{
  if(src.id()=="java-this")
    return convert_java_this(src, precedence=15);
  else if(src.id()==ID_side_effect &&
          (src.get(ID_statement)==ID_java_new ||
           src.get(ID_statement)==ID_java_new_array))
    return convert_java_new(src, precedence=15);
  else if(src.id()==ID_side_effect &&
          src.get(ID_statement)==ID_throw)
    return convert_function(src, "throw", precedence=16);
  else if(src.is_constant() && src.type().id() == ID_verilogbv)
    return "'" + id2string(src.get(ID_value)) + "'";
  else if(src.is_constant() && to_constant_expr(src).get_value()==ID_nullptr)
    return "nullptr";
  else if(src.id()==ID_unassigned)
    return "?";
  else if(src.id()=="pod_constructor")
    return "pod_constructor";
  else
    return expr2ct::convert(src, precedence);
}

/*******************************************************************\

Function: expr2javat::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2javat::convert_code(
  const codet &src,
  unsigned indent)
{
  const irep_idt &statement=src.get(ID_statement);

  if(statement==ID_java_new ||
     statement==ID_java_new_array)
    return convert_java_new(src,indent);

  return expr2ct::convert_code(src, indent);
}

/*******************************************************************\

Function: expr2java

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2java(const exprt &expr, const namespacet &ns)
{
  expr2javat expr2java(ns);
  expr2java.get_shorthands(expr);
  return expr2java.convert(expr);
}

/*******************************************************************\

Function: type2java

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2java(const typet &type, const namespacet &ns)
{
  expr2javat expr2java(ns);
  return expr2java.convert(type);
}
