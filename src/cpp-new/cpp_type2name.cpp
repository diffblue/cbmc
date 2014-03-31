/*******************************************************************\

Module: C++ Language Module

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <string>

#include <util/type.h>
#include <util/std_types.h>
#include <util/i2string.h>

/*******************************************************************\

Function: do_prefix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string do_prefix(const std::string &s)
{
  if(s.find(',')!=std::string::npos ||
     (s!="" && isdigit(s[0])))
    return i2string(s.size())+"_"+s;

  return s;
}

/*******************************************************************\

Function: irep2name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void irep2name(const irept &irep, std::string &result)
{
  result="";
  
  if(is_reference(static_cast<const typet&>(irep)))
    result+="reference";

  if(irep.id()!="")
    result+=do_prefix(irep.id_string());

  if(irep.get_named_sub().empty() &&
     irep.get_sub().empty() &&
     irep.get_comments().empty())
    return;

  result+="(";
  bool first=true;

  forall_named_irep(it, irep.get_named_sub())
  {
    if(first) first=false; else result+=",";

    result+=do_prefix(name2string(it->first));

    result+="=";
    std::string tmp;
    irep2name(it->second, tmp);
    result+=tmp;
  }

  forall_named_irep(it, irep.get_comments())
    if(it->first==ID_C_constant ||
       it->first==ID_C_volatile ||
       it->first==ID_C_restricted)
    {
      if(first) first=false; else result+=",";
      result+=do_prefix(name2string(it->first));
      result+="=";
      std::string tmp;
      irep2name(it->second, tmp);
      result+=tmp;
    }

  forall_irep(it, irep.get_sub())
  {
    if(first) first=false; else result+=",";
    std::string tmp;
    irep2name(*it, tmp);
    result+=tmp;
  }

  result+=")";
}

/*******************************************************************\

Function: cpp_type2name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_type2name(const typet &type)
{
  std::string result;

  if(type.get_bool(ID_C_constant) ||
     type.get(ID_C_qualifier)==ID_const)
    result+="const_";
  
  if(type.get_bool(ID_C_restricted))
    result+="restricted_";
  
  if(type.get_bool(ID_C_volatile))
    result+="volatile_";
    
  if(type.id()==ID_empty || type.id()==ID_void)
    result+="void";
  else if(type.id()==ID_bool)
    result+="bool";
  else if(type.id()==ID_pointer)
  {
    if(is_reference(type))
      result+="ref_"+cpp_type2name(type.subtype());
    else if(is_rvalue_reference(type))
      result+="rref_"+cpp_type2name(type.subtype());
    else
      result+="ptr_"+cpp_type2name(type.subtype());
  }
  else if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
  {
    // we try to use #c_type
    const irep_idt c_type=type.get(ID_C_c_type);
    
    if(c_type!=irep_idt())
      result+=id2string(c_type);
    else if(type.id()==ID_unsignedbv)
      result+="unsigned_int";
    else
      result+="signed_int";
  }
  else if(type.id()==ID_fixedbv || type.id()==ID_floatbv)
  {
    // we try to use #c_type
    const irep_idt c_type=type.get(ID_C_c_type);

    if(c_type!=irep_idt())
      result+=id2string(c_type);
    else
      result+="double";
  }
  else if(type.id()==ID_code)
  {
    // we do (args)->(return_type)
    const code_typet::argumentst &arguments=to_code_type(type).arguments();
    const typet &return_type=to_code_type(type).return_type();
    
    result+="(";

    for(code_typet::argumentst::const_iterator
        arg_it=arguments.begin();
        arg_it!=arguments.end();
        arg_it++)
    {
      if(arg_it!=arguments.begin()) result+=",";
      result+=cpp_type2name(arg_it->type());
    }
        
    result+=")";
    result+="->(";
    result+=cpp_type2name(return_type);
    result+=")";
  }
  else
  {
    // give up
    std::string tmp;
    irep2name(type, tmp);
    return tmp;
  }
  
  return result;
}

/*******************************************************************\

Function: cpp_expr2name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_expr2name(const exprt &expr)
{
  std::string tmp;
  irep2name(expr, tmp);
  return tmp;
}

