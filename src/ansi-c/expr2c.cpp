/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr2c.h"

#include <algorithm>
#include <cassert>
#include <sstream>

#include <map>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/find_symbols.h>
#include <util/fixedbv.h>
#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/suffix.h>
#include <util/symbol.h>

#include "c_misc.h"
#include "c_qualifiers.h"
#include "expr2c_class.h"

// clang-format off

expr2c_configurationt expr2c_configurationt::default_configuration
{
  true,
  true,
  true,
  "TRUE",
  "FALSE"
};

expr2c_configurationt expr2c_configurationt::clean_configuration
{
  false,
  false,
  false,
  "1",
  "0"
};

// clang-format on
/*

Precedences are as follows. Higher values mean higher precedence.

16 function call ()
   ++ -- [] . ->

1  comma

*/

irep_idt expr2ct::id_shorthand(const irep_idt &identifier) const
{
  const symbolt *symbol;

  if(!ns.lookup(identifier, symbol) &&
     !symbol->base_name.empty() &&
      has_suffix(id2string(identifier), id2string(symbol->base_name)))
    return symbol->base_name;

  std::string sh=id2string(identifier);

  std::string::size_type pos=sh.rfind("::");
  if(pos!=std::string::npos)
    sh.erase(0, pos+2);

  return sh;
}

static std::string clean_identifier(const irep_idt &id)
{
  std::string dest=id2string(id);

  std::string::size_type c_pos=dest.find("::");
  if(c_pos!=std::string::npos &&
     dest.rfind("::")==c_pos)
    dest.erase(0, c_pos+2);
  else if(c_pos!=std::string::npos)
  {
    for(std::string::iterator it2=dest.begin();
        it2!=dest.end();
        ++it2)
      if(*it2==':')
        *it2='$';
      else if(*it2=='-')
        *it2='_';
  }

  // rewrite . as used in ELF section names
  std::replace(dest.begin(), dest.end(), '.', '_');

  return dest;
}

void expr2ct::get_shorthands(const exprt &expr)
{
  find_symbols_sett symbols;
  find_symbols(expr, symbols);

  // avoid renaming parameters, if possible
  for(find_symbols_sett::const_iterator
      it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    const symbolt *symbol;
    bool is_param=!ns.lookup(*it, symbol) && symbol->is_parameter;

    if(!is_param)
      continue;

    irep_idt sh=id_shorthand(*it);

    std::string func = id2string(*it);
    func = func.substr(0, func.rfind("::"));

    // if there is a global symbol of the same name as the shorthand (even if
    // not present in this particular expression) then there is a collision
    const symbolt *global_symbol;
    if(!ns.lookup(sh, global_symbol))
      sh = func + "$$" + id2string(sh);

    ns_collision[func].insert(sh);

    if(!shorthands.insert(std::make_pair(*it, sh)).second)
      UNREACHABLE;
  }

  for(find_symbols_sett::const_iterator
      it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    if(shorthands.find(*it)!=shorthands.end())
      continue;

    irep_idt sh=id_shorthand(*it);

    bool has_collision=
      ns_collision[irep_idt()].find(sh)!=
      ns_collision[irep_idt()].end();

    if(!has_collision)
    {
      // if there is a global symbol of the same name as the shorthand (even if
      // not present in this particular expression) then there is a collision
      const symbolt *symbol;
      has_collision=!ns.lookup(sh, symbol);
    }

    if(!has_collision)
    {
      irep_idt func;

      const symbolt *symbol;
      if(!ns.lookup(*it, symbol))
        func=symbol->location.get_function();

      has_collision=!ns_collision[func].insert(sh).second;
    }

    if(has_collision)
      sh=clean_identifier(*it);

    shorthands.insert(std::make_pair(*it, sh));
  }
}

std::string expr2ct::convert(const typet &src)
{
  return convert_rec(src, c_qualifierst(), "");
}

std::string expr2ct::convert_rec(
  const typet &src,
  const qualifierst &qualifiers,
  const std::string &declarator)
{
  std::unique_ptr<qualifierst> clone = qualifiers.clone();
  c_qualifierst &new_qualifiers = dynamic_cast<c_qualifierst &>(*clone);
  new_qualifiers.read(src);

  std::string q=new_qualifiers.as_string();

  std::string d=
    declarator==""?declarator:" "+declarator;

  if(src.find(ID_C_typedef).is_not_nil())
  {
    return q+id2string(src.get(ID_C_typedef))+d;
  }

  if(src.id()==ID_bool)
  {
    return q + CPROVER_PREFIX + "bool" + d;
  }
  else if(src.id()==ID_c_bool)
  {
    return q+"_Bool"+d;
  }
  else if(src.id()==ID_string)
  {
    return q+"__CPROVER_string"+d;
  }
  else if(src.id()==ID_natural ||
          src.id()==ID_integer ||
          src.id()==ID_rational)
  {
    return q+src.id_string()+d;
  }
  else if(src.id()==ID_empty)
  {
    return q+"void"+d;
  }
  else if(src.id()==ID_complex)
  {
    // these take more or less arbitrary subtypes
    return q+"_Complex "+convert(src.subtype())+d;
  }
  else if(src.id()==ID_floatbv)
  {
    std::size_t width=to_floatbv_type(src).get_width();

    if(width==config.ansi_c.single_width)
      return q+"float"+d;
    else if(width==config.ansi_c.double_width)
      return q+"double"+d;
    else if(width==config.ansi_c.long_double_width)
      return q+"long double"+d;
    else
    {
      std::string swidth=src.get_string(ID_width);
      std::string fwidth=src.get_string(ID_f);
      return q+"__CPROVER_floatbv["+swidth+"]["+fwidth+"]";
    }
  }
  else if(src.id()==ID_fixedbv)
  {
    const std::size_t width=to_fixedbv_type(src).get_width();

    const std::size_t fraction_bits=to_fixedbv_type(src).get_fraction_bits();
    return
      q+"__CPROVER_fixedbv["+std::to_string(width)+"]["+
      std::to_string(fraction_bits)+"]"+d;
  }
  else if(src.id()==ID_c_bit_field)
  {
    std::string width=std::to_string(to_c_bit_field_type(src).get_width());
    return q+convert(src.subtype())+d+" : "+width;
  }
  else if(src.id()==ID_signedbv ||
          src.id()==ID_unsignedbv)
  {
    // annotated?
    irep_idt c_type=src.get(ID_C_c_type);
    const std::string c_type_str=c_type_as_string(c_type);

    if(c_type==ID_char &&
       config.ansi_c.char_is_unsigned!=(src.id()==ID_unsignedbv))
    {
      if(src.id()==ID_signedbv)
        return q+"signed char"+d;
      else
        return q+"unsigned char"+d;
    }
    else if(c_type!=ID_wchar_t && !c_type_str.empty())
      return q+c_type_str+d;

    // There is also wchar_t among the above, but this isn't a C type.

    mp_integer width=string2integer(src.get_string(ID_width));

    bool is_signed=src.id()==ID_signedbv;
    std::string sign_str=is_signed?"signed ":"unsigned ";

    if(width==config.ansi_c.int_width)
    {
      if(is_signed)
        sign_str="";
      return q+sign_str+"int"+d;
    }
    else if(width==config.ansi_c.long_int_width)
    {
      if(is_signed)
        sign_str="";
      return q+sign_str+"long int"+d;
    }
    else if(width==config.ansi_c.char_width)
    {
      // always include sign
      return q+sign_str+"char"+d;
    }
    else if(width==config.ansi_c.short_int_width)
    {
      if(is_signed)
        sign_str="";
      return q+sign_str+"short int"+d;
    }
    else if(width==config.ansi_c.long_long_int_width)
    {
      if(is_signed)
        sign_str="";
      return q+sign_str+"long long int"+d;
    }
    else if(width==128)
    {
      if(is_signed)
        sign_str="";
      return q+sign_str+"__int128";
    }
    else
    {
      return q+sign_str+
             "__CPROVER_bitvector["+integer2string(width)+"]"+d;
    }
  }
  else if(src.id()==ID_struct)
  {
    return convert_struct_type(src, q, d);
  }
  else if(src.id()==ID_incomplete_struct)
  {
    std::string dest=q+"struct";

    const std::string &tag=src.get_string(ID_tag);
    if(tag!="")
      dest+=" "+tag;
    dest+=d;

    return dest;
  }
  else if(src.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(src);

    std::string dest=q+"union";

    const irep_idt &tag=union_type.get_tag();
    if(tag!="")
      dest+=" "+id2string(tag);
    dest+=" {";

    for(const auto &c : union_type.components())
    {
      dest+=' ';
      dest += convert_rec(c.type(), c_qualifierst(), id2string(c.get_name()));
      dest+=';';
    }

    dest+=" }";

    dest+=d;

    return dest;
  }
  else if(src.id()==ID_incomplete_union)
  {
    std::string dest=q+"union";

    const std::string &tag=src.get_string(ID_tag);
    if(tag!="")
      dest+=" "+tag;
    dest+=d;

    return dest;
  }
  else if(src.id()==ID_c_enum)
  {
    std::string result;
    result+=q;
    result+="enum";

    // do we have a tag?
    const irept &tag=src.find(ID_tag);

    if(tag.is_nil())
    {
    }
    else
    {
      result+=' ';
      result+=tag.get_string(ID_C_base_name);
    }

    result+=' ';
    result+='{';

    // add members
    const c_enum_typet::memberst &members=to_c_enum_type(src).members();

    for(c_enum_typet::memberst::const_iterator
        it=members.begin();
        it!=members.end();
        it++)
    {
      if(it!=members.begin())
        result+=',';
      result+=' ';
      result+=id2string(it->get_base_name());
      result+='=';
      result+=id2string(it->get_value());
    }

    result+=" }";

    result+=d;
    return result;
  }
  else if(src.id()==ID_incomplete_c_enum)
  {
    const irept &tag=src.find(ID_tag);

    if(tag.is_not_nil())
    {
      std::string result=q+"enum";
      result+=" "+tag.get_string(ID_C_base_name);
      result+=d;
      return result;
    }
  }
  else if(src.id()==ID_c_enum_tag)
  {
    const c_enum_tag_typet &c_enum_tag_type=to_c_enum_tag_type(src);
    const symbolt &symbol=ns.lookup(c_enum_tag_type);
    std::string result=q+"enum";
    result+=" "+id2string(symbol.base_name);
    result+=d;
    return result;
  }
  else if(src.id()==ID_pointer)
  {
    c_qualifierst sub_qualifiers;
    sub_qualifiers.read(src.subtype());
    const typet &subtype_followed=ns.follow(src.subtype());

    // The star gets attached to the declarator.
    std::string new_declarator="*";

    if(q!="" &&
       (!declarator.empty() || subtype_followed.id()==ID_pointer))
      new_declarator+=" "+q;

    new_declarator+=declarator;

    // Depending on precedences, we may add parentheses.
    if(subtype_followed.id()==ID_code ||
        (sizeof_nesting==0 &&
         (subtype_followed.id()==ID_array ||
          subtype_followed.id()==ID_incomplete_array)))
      new_declarator="("+new_declarator+")";

    return convert_rec(src.subtype(), sub_qualifiers, new_declarator);
  }
  else if(src.id()==ID_array)
  {
    return convert_array_type(src, qualifiers, declarator);
  }
  else if(src.id()==ID_incomplete_array)
  {
    // The [] gets attached to the declarator.
    // This won't parse without declarator.
    return convert_rec(
      src.subtype(), qualifiers, declarator+"[]");
  }
  else if(src.id() == ID_symbol_type)
  {
    symbol_typet symbolic_type=to_symbol_type(src);
    const irep_idt &typedef_identifer=symbolic_type.get(ID_typedef);

    // Providing we have a valid identifer, we can just use that rather than
    // trying to find the concrete type
    if(typedef_identifer!="")
    {
      return q+id2string(typedef_identifer)+d;
    }
    else
    {
      const typet &followed=ns.follow(src);

      if(followed.id()==ID_struct)
      {
        std::string dest=q+"struct";
        const irep_idt &tag=to_struct_type(followed).get_tag();
        if(tag!="")
          dest+=" "+id2string(tag);
        dest+=d;
        return dest;
      }
      else if(followed.id()==ID_union)
      {
        std::string dest=q+"union";
        const irep_idt &tag=to_union_type(followed).get_tag();
        if(tag!="")
          dest+=" "+id2string(tag);
        dest+=d;
        return dest;
      }
      else
        return convert_rec(followed, new_qualifiers, declarator);
    }
  }
  else if(src.id()==ID_struct_tag)
  {
    const struct_tag_typet &struct_tag_type=
      to_struct_tag_type(src);

    std::string dest=q+"struct";
    const std::string &tag=ns.follow_tag(struct_tag_type).get_string(ID_tag);
    if(tag!="")
      dest+=" "+tag;
    dest+=d;

    return dest;
  }
  else if(src.id()==ID_union_tag)
  {
    const union_tag_typet &union_tag_type=
      to_union_tag_type(src);

    std::string dest=q+"union";
    const std::string &tag=ns.follow_tag(union_tag_type).get_string(ID_tag);
    if(tag!="")
      dest+=" "+tag;
    dest+=d;

    return dest;
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);

    // C doesn't really have syntax for function types,
    // i.e., the following won't parse without declarator
    std::string dest=declarator+"(";

    const code_typet::parameterst &parameters=code_type.parameters();

    if(parameters.empty())
    {
      if(code_type.has_ellipsis())
        dest+=""; // empty!
      else
        dest+="void"; // means 'no parameters'
    }
    else
    {
      for(code_typet::parameterst::const_iterator
          it=parameters.begin();
          it!=parameters.end();
          it++)
      {
        if(it!=parameters.begin())
          dest+=", ";

        if(it->get_identifier().empty())
          dest+=convert(it->type());
        else
        {
          std::string arg_declarator=
            convert(symbol_exprt(it->get_identifier(), it->type()));
          dest+=convert_rec(it->type(), c_qualifierst(), arg_declarator);
        }
      }

      if(code_type.has_ellipsis())
        dest+=", ...";
    }

    dest+=')';

    c_qualifierst ret_qualifiers;
    ret_qualifiers.read(code_type.return_type());
    // _Noreturn should go with the return type
    if(new_qualifiers.is_noreturn)
    {
      ret_qualifiers.is_noreturn=true;
      new_qualifiers.is_noreturn=false;
      q=new_qualifiers.as_string();
    }

    const typet &return_type=code_type.return_type();

    // return type may be a function pointer or array
    const typet *non_ptr_type=&ns.follow(return_type);
    while(non_ptr_type->id()==ID_pointer)
      non_ptr_type=&(ns.follow(non_ptr_type->subtype()));

    if(non_ptr_type->id()==ID_code ||
       non_ptr_type->id()==ID_array)
      dest=convert_rec(return_type, ret_qualifiers, dest);
    else
      dest=convert_rec(return_type, ret_qualifiers, "")+" "+dest;

    if(!q.empty())
    {
      dest+=" "+q;
      // strip trailing space off q
      if(dest[dest.size()-1]==' ')
        dest.resize(dest.size()-1);
    }

    return dest;
  }
  else if(src.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(src);

    mp_integer size_int;
    to_integer(vector_type.size(), size_int);

    std::string dest="__gcc_v"+integer2string(size_int);

    std::string tmp=convert(vector_type.subtype());

    if(tmp=="signed char" || tmp=="char")
      dest+="qi";
    else if(tmp=="signed short int")
      dest+="hi";
    else if(tmp=="signed int")
      dest+="si";
    else if(tmp=="signed long long int")
      dest+="di";
    else if(tmp=="float")
      dest+="sf";
    else if(tmp=="double")
      dest+="df";
    else
    {
      const std::string subtype=convert(vector_type.subtype());
      dest=subtype;
      dest+=" __attribute__((vector_size (";
      dest+=convert(vector_type.size());
      dest+="*sizeof("+subtype+"))))";
    }

    return q+dest+d;
  }
  else if(src.id()==ID_gcc_builtin_va_list)
  {
    return q+"__builtin_va_list"+d;
  }
  else if(src.id()==ID_constructor ||
          src.id()==ID_destructor)
  {
    return q+"__attribute__(("+id2string(src.id())+")) void"+d;
  }

  {
    lispexprt lisp;
    irep2lisp(src, lisp);
    std::string dest="irep(\""+MetaString(lisp.expr2string())+"\")";
    dest+=d;

    return dest;
  }
}

/// To generate C-like string for defining the given struct
/// \param src: the struct type being converted
/// \param qualifiers: any qualifiers on the type
/// \param declarator: the declarator on the type
/// \return Returns a type declaration for a struct, containing the body of the
///   struct and in that body the padding parameters.
std::string expr2ct::convert_struct_type(
  const typet &src,
  const std::string &qualifiers_str,
  const std::string &declarator_str)
{
  return convert_struct_type(
    src,
    qualifiers_str,
    declarator_str,
    configuration.print_struct_body_in_type,
    configuration.include_struct_padding_components);
}

/// To generate C-like string for declaring (or defining) the given struct
/// \param src: the struct type being converted
/// \param qualifiers: any qualifiers on the type
/// \param declarator: the declarator on the type
/// \param inc_struct_body: when generating the code, should we include a
///   complete definition of the struct
/// \param inc_padding_components: should the padding parameters be included
///   Note this only makes sense if inc_struct_body
/// \return Returns a type declaration for a struct, optionally containing the
///   body of the struct (and in that body, optionally the padding parameters).
std::string expr2ct::convert_struct_type(
  const typet &src,
  const std::string &qualifiers,
  const std::string &declarator,
  bool inc_struct_body,
  bool inc_padding_components)
{
  // Either we are including the body (in which case it makes sense to include
  // or exclude the parameters) or there is no body so therefore we definitely
  // shouldn't be including the parameters
  assert(inc_struct_body || !inc_padding_components);

  const struct_typet &struct_type=to_struct_type(src);

  std::string dest=qualifiers+"struct";

  const irep_idt &tag=struct_type.get_tag();
  if(tag!="")
    dest+=" "+id2string(tag);

  if(inc_struct_body)
  {
    dest+=" {";

    for(const auto &component : struct_type.components())
    {
      // Skip padding parameters unless we including them
      if(component.get_is_padding() && !inc_padding_components)
      {
        continue;
      }

      dest+=' ';
      dest+=convert_rec(
        component.type(),
        c_qualifierst(),
        id2string(component.get_name()));
      dest+=';';
    }

    dest+=" }";
  }

  dest+=declarator;

  return dest;
}

/// To generate a C-like type declaration of an array. Includes the size of the
/// array in the []
/// \param src: The array type to convert
/// qualifier
/// declarator_str
/// \return A C-like type declaration of an array
std::string expr2ct::convert_array_type(
  const typet &src,
  const qualifierst &qualifiers,
  const std::string &declarator_str)
{
  return convert_array_type(
    src, qualifiers, declarator_str, configuration.include_array_size);
}

/// To generate a C-like type declaration of an array. Optionally can include or
/// exclude the size of the array in the []
/// \param src: The array type to convert
/// qualifier
/// declarator_str
/// \param inc_size_if_possible: Should the generated string include the size of
///   the array (if it is known).
/// \return A C-like type declaration of an array
std::string expr2ct::convert_array_type(
  const typet &src,
  const qualifierst &qualifiers,
  const std::string &declarator_str,
  bool inc_size_if_possible)
{
  // The [...] gets attached to the declarator.
  std::string array_suffix;

  if(to_array_type(src).size().is_nil() || !inc_size_if_possible)
    array_suffix="[]";
  else
    array_suffix="["+convert(to_array_type(src).size())+"]";

  // This won't really parse without declarator.
  // Note that qualifiers are passed down.
  return convert_rec(
    src.subtype(), qualifiers, declarator_str+array_suffix);
}

std::string expr2ct::convert_typecast(
  const typecast_exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  // some special cases

  const typet &to_type=ns.follow(src.type());
  const typet &from_type=ns.follow(src.op().type());

  if(to_type.id()==ID_c_bool &&
     from_type.id()==ID_bool)
    return convert_with_precedence(src.op(), precedence);

  if(to_type.id()==ID_bool &&
     from_type.id()==ID_c_bool)
    return convert_with_precedence(src.op(), precedence);

  std::string dest="("+convert(src.type())+")";

  unsigned p;
  std::string tmp=convert_with_precedence(src.op(), p);

  if(precedence>p)
    dest+='(';
  dest+=tmp;
  if(precedence>p)
    dest+=')';

  return dest;
}

std::string expr2ct::convert_trinary(
  const exprt &src,
  const std::string &symbol1,
  const std::string &symbol2,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  const exprt &op0=src.op0();
  const exprt &op1=src.op1();
  const exprt &op2=src.op2();

  unsigned p0, p1, p2;

  std::string s_op0=convert_with_precedence(op0, p0);
  std::string s_op1=convert_with_precedence(op1, p1);
  std::string s_op2=convert_with_precedence(op2, p2);

  std::string dest;

  if(precedence>=p0)
    dest+='(';
  dest+=s_op0;
  if(precedence>=p0)
    dest+=')';

  dest+=' ';
  dest+=symbol1;
  dest+=' ';

  if(precedence>=p1)
    dest+='(';
  dest+=s_op1;
  if(precedence>=p1)
    dest+=')';

  dest+=' ';
  dest+=symbol2;
  dest+=' ';

  if(precedence>=p2)
    dest+='(';
  dest+=s_op2;
  if(precedence>=p2)
    dest+=')';

  return dest;
}

std::string expr2ct::convert_quantifier(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p0, p1;

  std::string op0=convert_with_precedence(src.op0(), p0);
  std::string op1=convert_with_precedence(src.op1(), p1);

  std::string dest=symbol+" { ";
  dest+=convert(src.op0().type());
  dest+=" "+op0+"; ";
  dest+=op1;
  dest+=" }";

  return dest;
}

std::string expr2ct::convert_with(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()<3)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert_with_precedence(src.op0(), p0);

  std::string dest;

  if(precedence>p0)
    dest+='(';
  dest+=op0;
  if(precedence>p0)
    dest+=')';

  dest+=" WITH [";

  for(size_t i=1; i<src.operands().size(); i+=2)
  {
    std::string op1, op2;
    unsigned p1, p2;

    if(i!=1)
      dest+=", ";

    if(src.operands()[i].id()==ID_member_name)
    {
      const irep_idt &component_name=
        src.operands()[i].get(ID_component_name);

      const typet &full_type=ns.follow(src.op0().type());

      const struct_union_typet &struct_union_type=
        to_struct_union_type(full_type);

      const struct_union_typet::componentt &comp_expr=
        struct_union_type.get_component(component_name);

      assert(comp_expr.is_not_nil());

      irep_idt display_component_name;

      if(comp_expr.get_pretty_name().empty())
        display_component_name=component_name;
      else
        display_component_name=comp_expr.get_pretty_name();

      op1="."+id2string(display_component_name);
      p1=10;
    }
    else
      op1=convert_with_precedence(src.operands()[i], p1);

    op2=convert_with_precedence(src.operands()[i+1], p2);

    dest+=op1;
    dest+=":=";
    dest+=op2;
  }

  dest+=']';

  return dest;
}

std::string expr2ct::convert_let(
  const let_exprt &src,
  unsigned precedence)
{
  if(src.operands().size()<3)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert_with_precedence(src.op0(), p0);

  std::string dest="LET ";
  dest+=convert(src.symbol());
  dest+='=';
  dest+=convert(src.value());
  dest+=" IN ";
  dest+=convert(src.where());

  return dest;
}

std::string expr2ct::convert_update(
  const exprt &src,
  unsigned precedence)
{
  // needs exactly 3 operands
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest;

  dest+="UPDATE(";

  std::string op0, op1, op2;
  unsigned p0, p2;

  op0=convert_with_precedence(src.op0(), p0);
  op2=convert_with_precedence(src.op2(), p2);

  if(precedence>p0)
    dest+='(';
  dest+=op0;
  if(precedence>p0)
    dest+=')';

  dest+=", ";

  const exprt &designator=src.op1();

  forall_operands(it, designator)
    dest+=convert(*it);

  dest+=", ";

  if(precedence>p2)
    dest+='(';
  dest+=op2;
  if(precedence>p2)
    dest+=')';

  dest+=')';

  return dest;
}

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
    std::string op=convert_with_precedence(*it, p);

    if(condition)
      dest+="  ";

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

std::string expr2ct::convert_binary(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence,
  bool full_parentheses)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  const exprt &op0=src.op0();
  const exprt &op1=src.op1();

  unsigned p0, p1;

  std::string s_op0=convert_with_precedence(op0, p0);
  std::string s_op1=convert_with_precedence(op1, p1);

  std::string dest;

  // In pointer arithmetic, x+(y-z) is unfortunately
  // not the same as (x+y)-z, even though + and -
  // have the same precedence. We thus add parentheses
  // for the case x+(y-z). Similarly, (x*y)/z is not
  // the same as x*(y/z), but * and / have the same
  // precedence.

  bool use_parentheses0=
    precedence>p0 ||
    (precedence==p0 && full_parentheses) ||
    (precedence==p0 && src.id()!=op0.id());

  if(use_parentheses0)
    dest+='(';
  dest+=s_op0;
  if(use_parentheses0)
    dest+=')';

  dest+=' ';
  dest+=symbol;
  dest+=' ';

  bool use_parentheses1=
    precedence>p1 ||
    (precedence==p1 && full_parentheses) ||
    (precedence==p1 && src.id()!=op1.id());

  if(use_parentheses1)
    dest+='(';
  dest+=s_op1;
  if(use_parentheses1)
    dest+=')';

  return dest;
}

std::string expr2ct::convert_multi_ary(
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
      if(symbol!=", ")
        dest+=' ';
      dest+=symbol;
      dest+=' ';
    }

    unsigned p;
    std::string op=convert_with_precedence(*it, p);

    // In pointer arithmetic, x+(y-z) is unfortunately
    // not the same as (x+y)-z, even though + and -
    // have the same precedence. We thus add parentheses
    // for the case x+(y-z). Similarly, (x*y)/z is not
    // the same as x*(y/z), but * and / have the same
    // precedence.

    bool use_parentheses=
      precedence>p ||
      (precedence==p && full_parentheses) ||
      (precedence==p && src.id()!=it->id());

    if(use_parentheses)
      dest+='(';
    dest+=op;
    if(use_parentheses)
      dest+=')';
  }

  return dest;
}

std::string expr2ct::convert_unary(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert_with_precedence(src.op0(), p);

  std::string dest=symbol;
  if(precedence>=p ||
     (!symbol.empty() && has_prefix(op, symbol)))
    dest+='(';
  dest+=op;
  if(precedence>=p ||
     (!symbol.empty() && has_prefix(op, symbol)))
    dest+=')';

  return dest;
}

std::string expr2ct::convert_allocate(const exprt &src, unsigned &precedence)
{
  if(src.operands().size() != 2)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0 = convert_with_precedence(src.op0(), p0);

  unsigned p1;
  std::string op1 = convert_with_precedence(src.op1(), p1);

  std::string dest = "ALLOCATE";
  dest += '(';

  if(src.type().id()==ID_pointer &&
     src.type().subtype().id()!=ID_empty)
  {
    dest+=convert(src.type().subtype());
    dest+=", ";
  }

  dest += op0 + ", " + op1;
  dest += ')';

  return dest;
}

std::string expr2ct::convert_nondet(
  const exprt &src,
  unsigned &precedence)
{
  if(!src.operands().empty())
    return convert_norep(src, precedence);

  return "NONDET("+convert(src.type())+")";
}

std::string expr2ct::convert_statement_expression(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()!=1 ||
     to_code(src.op0()).get_statement()!=ID_block)
    return convert_norep(src, precedence);

  return "("+convert_code(to_code_block(to_code(src.op0())), 0)+")";
}

std::string expr2ct::convert_prob_coin(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
    return "COIN("+convert(src.op0())+")";
  else
    return convert_norep(src, precedence);
}

std::string expr2ct::convert_literal(
  const exprt &src,
  unsigned &precedence)
{
  return "L("+src.get_string(ID_literal)+")";
}

std::string expr2ct::convert_prob_uniform(
  const exprt &src,
  unsigned &precedence)
{
  if(src.operands().size()==1)
    return "PROB_UNIFORM("+convert(src.type())+","+convert(src.op0())+")";
  else
    return convert_norep(src, precedence);
}

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
    std::string op=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";

    dest+=op;
  }

  dest+=')';

  return dest;
}

std::string expr2ct::convert_comma(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert_with_precedence(src.op0(), p0);
  if(*op0.rbegin()==';')
    op0.resize(op0.size()-1);

  unsigned p1;
  std::string op1=convert_with_precedence(src.op1(), p1);
  if(*op1.rbegin()==';')
    op1.resize(op1.size()-1);

  std::string dest=op0;
  dest+=", ";
  dest+=op1;

  return dest;
}

std::string expr2ct::convert_complex(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()==2 &&
     src.op0().is_zero() &&
     src.op1().id()==ID_constant)
  {
    // This is believed to be gcc only; check if this is sensible
    // in MSC mode.
    return convert_with_precedence(src.op1(), precedence)+"i";
  }

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
    std::string op=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";

    dest+=op;
  }

  dest+=')';

  return dest;
}

std::string expr2ct::convert_array_of(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "ARRAY_OF("+convert(src.op0())+')';
}

std::string expr2ct::convert_byte_extract(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert_with_precedence(src.op0(), p0);

  unsigned p1;
  std::string op1=convert_with_precedence(src.op1(), p1);

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

std::string expr2ct::convert_byte_update(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  unsigned p0;
  std::string op0=convert_with_precedence(src.op0(), p0);

  unsigned p1;
  std::string op1=convert_with_precedence(src.op1(), p1);

  unsigned p2;
  std::string op2=convert_with_precedence(src.op2(), p2);

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

std::string expr2ct::convert_unary_post(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert_with_precedence(src.op0(), p);

  std::string dest;
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';
  dest+=symbol;

  return dest;
}

std::string expr2ct::convert_index(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  unsigned p;
  std::string op=convert_with_precedence(src.op0(), p);

  std::string dest;
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';

  dest+='[';
  dest+=convert(src.op1());
  dest+=']';

  return dest;
}

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

  op=convert_with_precedence(src.op0(), p);
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';

  dest+=", ";

  op=convert_with_precedence(src.op1(), p);
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';

  dest+=')';

  return dest;
}

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

  op=convert_with_precedence(src.op0(), p);
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';

  dest+=", ";

  op=convert_with_precedence(src.op1(), p);
  if(precedence>p)
    dest+='(';
  dest+=op;
  if(precedence>p)
    dest+=')';

  dest+=')';

  return dest;
}

std::string expr2ct::convert_member_designator(const exprt &src)
{
  unsigned precedence;

  if(!src.operands().empty())
    return convert_norep(src, precedence);

  return "."+src.get_string(ID_component_name);
}

std::string expr2ct::convert_index_designator(const exprt &src)
{
  unsigned precedence;

  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "["+convert(src.op0())+"]";
}

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
    std::string op=convert_with_precedence(src.op0().op0(), p);

    if(precedence>p || src.op0().op0().id()==ID_typecast)
      dest+='(';
    dest+=op;
    if(precedence>p || src.op0().op0().id()==ID_typecast)
      dest+=')';

    dest+="->";
  }
  else
  {
    std::string op=convert_with_precedence(src.op0(), p);

    if(precedence>p || src.op0().id()==ID_typecast)
      dest+='(';
    dest+=op;
    if(precedence>p || src.op0().id()==ID_typecast)
      dest+=')';

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

    if(!comp_expr.get(ID_pretty_name).empty())
      dest+=comp_expr.get_string(ID_pretty_name);
    else
      dest+=id2string(component_name);

    return dest;
  }

  std::size_t n=src.get_component_number();

  if(n>=struct_union_type.components().size())
    return convert_norep(src, precedence);

  const exprt comp_expr=
    struct_union_type.components()[n];

  dest+=comp_expr.get_string(ID_pretty_name);

  return dest;
}

std::string expr2ct::convert_array_member_value(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "[]="+convert(src.op0());
}

std::string expr2ct::convert_struct_member_value(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  return "."+src.get_string(ID_name)+"="+convert(src.op0());
}

std::string expr2ct::convert_norep(
  const exprt &src,
  unsigned &precedence)
{
  lispexprt lisp;
  irep2lisp(src, lisp);
  std::string dest="irep(\""+MetaString(lisp.expr2string())+"\")";
  precedence=16;
  return dest;
}

std::string expr2ct::convert_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const irep_idt &id=src.get(ID_identifier);
  std::string dest;

  if(src.operands().size()==1 &&
     src.op0().id()==ID_predicate_passive_symbol)
    dest=src.op0().get_string(ID_identifier);
  else
  {
    std::unordered_map<irep_idt, irep_idt>::const_iterator entry =
      shorthands.find(id);
    // we might be called from conversion of a type
    if(entry==shorthands.end())
    {
      get_shorthands(src);

      entry=shorthands.find(id);
      assert(entry!=shorthands.end());
    }

    dest=id2string(entry->second);

    #if 0
    if(has_prefix(id2string(id), "symex_dynamic::dynamic_object"))
    {
      if(sizeof_nesting++ == 0)
        dest+=" /*"+convert(src.type());
      if(--sizeof_nesting == 0)
        dest+="*/";
    }
    #endif
  }

  if(src.id()==ID_next_symbol)
    dest="NEXT("+dest+")";

  return dest;
}

std::string expr2ct::convert_nondet_symbol(
  const nondet_symbol_exprt &src,
  unsigned &precedence)
{
  const irep_idt id=src.get_identifier();
  return "nondet_symbol("+id2string(id)+")";
}

std::string expr2ct::convert_predicate_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "ps("+id+")";
}

std::string expr2ct::convert_predicate_next_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "pns("+id+")";
}

std::string expr2ct::convert_predicate_passive_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return "pps("+id+")";
}

std::string expr2ct::convert_quantified_symbol(
  const exprt &src,
  unsigned &precedence)
{
  const std::string &id=src.get_string(ID_identifier);
  return id;
}

std::string expr2ct::convert_nondet_bool(
  const exprt &src,
  unsigned &precedence)
{
  return "nondet_bool()";
}

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
    result+='?';
  else
    result+=convert(src.type());

  result+='>';

  return result;
}

std::string expr2ct::convert_constant(
  const constant_exprt &src,
  unsigned &precedence)
{
  const irep_idt &base=src.get(ID_C_base);
  const typet &type=ns.follow(src.type());
  const irep_idt value=src.get_value();
  std::string dest;

  if(type.id()==ID_integer ||
     type.id()==ID_natural ||
     type.id()==ID_rational)
  {
    dest=id2string(value);
  }
  else if(type.id()==ID_c_enum ||
          type.id()==ID_c_enum_tag)
  {
    typet c_enum_type=
      type.id()==ID_c_enum?to_c_enum_type(type):
                           ns.follow_tag(to_c_enum_tag_type(type));

    if(c_enum_type.id()!=ID_c_enum)
      return convert_norep(src, precedence);

    const bool is_signed = c_enum_type.subtype().id() == ID_signedbv;
    const auto width = to_bitvector_type(c_enum_type.subtype()).get_width();

    mp_integer int_value = bvrep2integer(value, width, is_signed);
    mp_integer i=0;

    irep_idt int_value_string=integer2string(int_value);

    const c_enum_typet::memberst &members=
      to_c_enum_type(c_enum_type).members();

    for(c_enum_typet::memberst::const_iterator
        it=members.begin();
        it!=members.end();
        it++)
    {
      if(it->get_value()==int_value_string)
        return "/*enum*/"+id2string(it->get_base_name());
    }

    // failed...
    return "/*enum*/"+integer2string(int_value);
  }
  else if(type.id()==ID_rational)
    return convert_norep(src, precedence);
  else if(type.id()==ID_bv)
  {
    // not C
    dest=id2string(value);
  }
  else if(type.id()==ID_bool)
  {
    dest=convert_constant_bool(src.is_true());
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_bit_field ||
          type.id()==ID_c_bool)
  {
    const auto width = to_bitvector_type(type).get_width();

    mp_integer int_value =
      bvrep2integer(value, width, type.id() == ID_signedbv);

    const irep_idt &c_type=
      type.id()==ID_c_bit_field?type.subtype().get(ID_C_c_type):
                 type.get(ID_C_c_type);

    if(type.id()==ID_c_bool)
    {
      dest=convert_constant_bool(int_value!=0);
    }
    else if(type==char_type() &&
            type!=signed_int_type() &&
            type!=unsigned_int_type())
    {
      if(int_value=='\n')
        dest+="'\\n'";
      else if(int_value=='\r')
        dest+="'\\r'";
      else if(int_value=='\t')
        dest+="'\\t'";
      else if(int_value=='\'')
        dest+="'\\''";
      else if(int_value=='\\')
        dest+="'\\\\'";
      else if(int_value>=' ' && int_value<126)
      {
        dest+='\'';
        dest+=static_cast<char>(integer2ulong(int_value));
        dest+='\'';
      }
      else
        dest=integer2string(int_value);
    }
    else
    {
      if(base=="16")
        dest="0x"+integer2string(int_value, 16);
      else if(base=="8")
        dest="0"+integer2string(int_value, 8);
      else if(base=="2")
        dest="0b"+integer2string(int_value, 2);
      else
        dest=integer2string(int_value);

      if(c_type==ID_unsigned_int)
        dest+='u';
      else if(c_type==ID_unsigned_long_int)
        dest+="ul";
      else if(c_type==ID_signed_long_int)
        dest+='l';
      else if(c_type==ID_unsigned_long_long_int)
        dest+="ull";
      else if(c_type==ID_signed_long_long_int)
        dest+="ll";

      if(src.find(ID_C_c_sizeof_type).is_not_nil() &&
         sizeof_nesting==0)
      {
        const exprt sizeof_expr = build_sizeof_expr(to_constant_expr(src), ns);

        if(sizeof_expr.is_not_nil())
        {
          ++sizeof_nesting;
          dest=convert(sizeof_expr)+" /*"+dest+"*/ ";
          --sizeof_nesting;
        }
      }
    }
  }
  else if(type.id()==ID_floatbv)
  {
    dest=ieee_floatt(to_constant_expr(src)).to_ansi_c_string();

    if(dest!="" && isdigit(dest[dest.size()-1]))
    {
      if(dest.find('.')==std::string::npos)
        dest+=".0";

      // ANSI-C: double is default; float/long-double require annotation
      if(src.type()==float_type())
        dest+='f';
      else if(src.type()==long_double_type() &&
              double_type()!=long_double_type())
        dest+='l';
    }
    else if(dest.size()==4 &&
            (dest[0]=='+' || dest[0]=='-'))
    {
      if(dest=="+inf")
        dest="+INFINITY";
      else if(dest=="-inf")
        dest="-INFINITY";
      else if(dest=="+NaN")
        dest="+NAN";
      else if(dest=="-NaN")
        dest="-NAN";
    }
  }
  else if(type.id()==ID_fixedbv)
  {
    dest=fixedbvt(to_constant_expr(src)).to_ansi_c_string();

    if(dest!="" && isdigit(dest[dest.size()-1]))
    {
      if(src.type()==float_type())
        dest+='f';
      else if(src.type()==long_double_type())
        dest+='l';
    }
  }
  else if(type.id()==ID_array ||
          type.id()==ID_incomplete_array)
  {
    dest=convert_array(src, precedence);
  }
  else if(type.id()==ID_pointer)
  {
    const irep_idt &value=to_constant_expr(src).get_value();

    if(value==ID_NULL)
    {
      dest="NULL";
      if(type.subtype().id()!=ID_empty)
        dest="(("+convert(type)+")"+dest+")";
    }
    else if(value==std::string(value.size(), '0') &&
            config.ansi_c.NULL_is_zero)
    {
      dest="NULL";
      if(type.subtype().id()!=ID_empty)
        dest="(("+convert(type)+")"+dest+")";
    }
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
        return convert_with_precedence(src.op0(), precedence);
    }
  }
  else if(type.id()==ID_string)
  {
    return '"'+id2string(src.get_value())+'"';
  }
  else
    return convert_norep(src, precedence);

  return dest;
}

/// To get the C-like representation of a given boolean value.
/// \param boolean_value: The value of the constant bool expression
/// \return Returns a C-like representation of the boolean value, e.g. TRUE or
///   FALSE.
std::string expr2ct::convert_constant_bool(bool boolean_value)
{
  if(boolean_value)
    return configuration.true_string;
  else
    return configuration.false_string;
}

std::string expr2ct::convert_struct(
  const exprt &src,
  unsigned &precedence)
{
  return convert_struct(
    src, precedence, configuration.include_struct_padding_components);
}

/// To generate a C-like string representing a struct. Can optionally include
/// the padding parameters.
/// \param src: The struct declaration expression
/// precedence
/// \param include_padding_components: Should the generated C code include the
///   padding members added to structs for GOTOs benefit
/// \return A string representation of the struct expression
std::string expr2ct::convert_struct(
  const exprt &src,
  unsigned &precedence,
  bool include_padding_components)
{
  const typet full_type=ns.follow(src.type());

  if(full_type.id()!=ID_struct)
    return convert_norep(src, precedence);

  const struct_typet &struct_type=
    to_struct_type(full_type);

  const struct_typet::componentst &components=
    struct_type.components();

  if(components.size()!=src.operands().size())
    return convert_norep(src, precedence);

  std::string dest="{ ";

  exprt::operandst::const_iterator o_it=src.operands().begin();

  bool first=true;
  bool newline=false;
  size_t last_size=0;

  for(const auto &component : struct_type.components())
  {
    if(o_it->type().id()==ID_code)
      continue;

    if(component.get_is_padding() && !include_padding_components)
    {
      ++o_it;
      continue;
    }

    if(first)
      first=false;
    else
    {
      dest+=',';

      if(newline)
        dest+="\n    ";
      else
        dest+=' ';
    }

    std::string tmp=convert(*o_it);

    if(last_size+40<dest.size())
    {
      newline=true;
      last_size=dest.size();
    }
    else
      newline=false;

    dest+='.';
    dest+=component.get_string(ID_name);
    dest+='=';
    dest+=tmp;

    o_it++;
  }

  dest+=" }";

  return dest;
}

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
  size_t last_size=0;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      dest+=',';

      if(newline)
        dest+="\n    ";
      else
        dest+=' ';
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

std::string expr2ct::convert_union(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest="{ ";

  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  std::string tmp=convert(src.op0());

  dest+='.';
  dest+=src.get_string(ID_component_name);
  dest+='=';
  dest+=tmp;

  dest+=" }";

  return dest;
}

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
      dest+='L';

    dest+="\"";

    dest.reserve(dest.size()+1+src.operands().size());

    bool last_was_hex=false;

    forall_operands(it, src)
    {
      // these have a trailing zero
      if(it==--src.operands().end())
        break;

      const unsigned int ch = numeric_cast_v<unsigned>(*it);

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
      case '\\': dest+="\\\\"; break;
      case '"': dest+="\\\""; break;

      default:
        if(ch>=' ' && ch!=127 && ch<0xff)
          dest+=static_cast<char>(ch);
        else
        {
          std::ostringstream oss;
          oss << "\\x" << std::hex << ch;
          dest += oss.str();
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
      if(tmp.size()>40)
        tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

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
      if(tmp.size()>40)
        tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return dest;
}

std::string expr2ct::convert_initializer_list(
  const exprt &src,
  unsigned &precedence)
{
  std::string dest;
  if(src.id()!=ID_compound_literal)
    dest+="{ ";

  forall_operands(it, src)
  {
    std::string tmp=convert(*it);

    if((it+1)!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40)
        tmp+="\n    ";
    }

    dest+=tmp;
  }

  if(src.id()!=ID_compound_literal)
    dest+=" }";

  return dest;
}

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
  dest+='=';
  dest+=convert(src.op0());

  return dest;
}

std::string expr2ct::convert_function_application(
  const function_application_exprt &src,
  unsigned &precedence)
{
  std::string dest;

  {
    unsigned p;
    std::string function_str=convert_with_precedence(src.function(), p);
    dest+=function_str;
  }

  dest+='(';

  forall_expr(it, src.arguments())
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.arguments().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=')';

  return dest;
}

std::string expr2ct::convert_side_effect_expr_function_call(
  const side_effect_expr_function_callt &src,
  unsigned &precedence)
{
  std::string dest;

  {
    unsigned p;
    std::string function_str=convert_with_precedence(src.function(), p);
    dest+=function_str;
  }

  dest+='(';

  forall_expr(it, src.arguments())
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.arguments().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=')';

  return dest;
}

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
    std::string arg_str=convert_with_precedence(*it, p);

    dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=')';

  return dest;
}

std::string expr2ct::indent_str(unsigned indent)
{
  return std::string(indent, ' ');
}

std::string expr2ct::convert_code_asm(
  const code_asmt &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);

  if(src.get_flavor()==ID_gcc)
  {
    if(src.operands().size()==5)
    {
      dest+="asm(";
      dest+=convert(src.op0());
      if(!src.operands()[1].operands().empty() ||
         !src.operands()[2].operands().empty() ||
         !src.operands()[3].operands().empty() ||
         !src.operands()[4].operands().empty())
      {
        // need extended syntax

        // outputs
        dest+=" : ";
        forall_operands(it, src.op1())
        {
          if(it->operands().size()==2)
          {
            if(it!=src.op1().operands().begin())
              dest+=", ";
            dest+=convert(it->op0());
            dest+="(";
            dest+=convert(it->op1());
            dest+=")";
          }
        }

        // inputs
        dest+=" : ";
        forall_operands(it, src.op2())
        {
          if(it->operands().size()==2)
          {
            if(it!=src.op2().operands().begin())
              dest+=", ";
            dest+=convert(it->op0());
            dest+="(";
            dest+=convert(it->op1());
            dest+=")";
          }
        }

        // clobbered registers
        dest+=" : ";
        forall_operands(it, src.op3())
        {
          if(it!=src.op3().operands().begin())
            dest+=", ";
          if(it->id()==ID_gcc_asm_clobbered_register)
            dest+=convert(it->op0());
          else
            dest+=convert(*it);
        }
      }
      dest+=");";
    }
  }
  else if(src.get_flavor()==ID_msc)
  {
    if(src.operands().size()==1)
    {
      dest+="__asm {\n";
      dest+=indent_str(indent);
      dest+=convert(src.op0());
      dest+="\n}";
    }
  }

  return dest;
}

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
    dest+=convert_code(
        src.body(),
        src.body().get_statement()==ID_block ? indent : indent+2);
  }

  return dest;
}

std::string expr2ct::convert_code_dowhile(
  const code_dowhilet &src,
  unsigned indent)
{
  if(src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);

  if(src.body().is_nil())
    dest+="do;";
  else
  {
    dest+="do\n";
    dest+=convert_code(
        src.body(),
        src.body().get_statement()==ID_block ? indent : indent+2);
    dest+="\n";
    dest+=indent_str(indent);
  }

  dest+="while("+convert(src.cond())+");";

  return dest;
}

std::string expr2ct::convert_code_ifthenelse(
  const code_ifthenelset &src,
  unsigned indent)
{
  if(src.operands().size()!=3)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="if("+convert(src.cond())+")\n";

  if(src.then_case().is_nil())
  {
    dest+=indent_str(indent+2);
    dest+=';';
  }
  else
    dest += convert_code(
      src.then_case(),
      src.then_case().get_statement() == ID_block ? indent : indent + 2);
  dest+="\n";

  if(!src.else_case().is_nil())
  {
    dest+="\n";
    dest+=indent_str(indent);
    dest+="else\n";
    dest += convert_code(
      src.else_case(),
      src.else_case().get_statement() == ID_block ? indent : indent + 2);
  }

  return dest;
}

std::string expr2ct::convert_code_return(
  const codet &src,
  unsigned indent)
{
  if(!src.operands().empty() &&
     src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="return";

  if(to_code_return(src).has_return_value())
    dest+=" "+convert(src.op0());

  dest+=';';

  return dest;
}

std::string expr2ct::convert_code_goto(
  const codet &src,
  unsigned indent)
{
  std:: string dest=indent_str(indent);
  dest+="goto ";
  dest+=clean_identifier(src.get(ID_destination));
  dest+=';';

  return dest;
}

std::string expr2ct::convert_code_break(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="break";
  dest+=';';

  return dest;
}

std::string expr2ct::convert_code_switch(
  const codet &src,
  unsigned indent)
{
  if(src.operands().empty())
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string dest=indent_str(indent);
  dest+="switch(";
  dest+=convert(src.op0());
  dest+=")\n";

  dest+=indent_str(indent);
  dest+='{';

  forall_operands(it, src)
  {
    if(it==src.operands().begin())
      continue;
    const exprt &op=*it;

    if(op.get(ID_statement)!=ID_block)
    {
      unsigned precedence;
      dest+=convert_norep(op, precedence);
    }
    else
    {
      forall_operands(it2, op)
        dest+=convert_code(to_code(*it2), indent+2);
    }
  }

  dest+="\n";
  dest+=indent_str(indent);
  dest+='}';

  return dest;
}

std::string expr2ct::convert_code_continue(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="continue";
  dest+=';';

  return dest;
}

std::string expr2ct::convert_code_decl(
  const codet &src,
  unsigned indent)
{
  // initializer to go away
  if(src.operands().size()!=1 &&
     src.operands().size()!=2)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  std::string declarator=convert(src.op0());

  std::string dest=indent_str(indent);

  const symbolt *symbol=nullptr;
  if(!ns.lookup(to_symbol_expr(src.op0()).get_identifier(), symbol))
  {
    if(symbol->is_file_local &&
       (src.op0().type().id()==ID_code || symbol->is_static_lifetime))
      dest+="static ";
    else if(symbol->is_extern)
      dest+="extern ";
    else if(
      symbol->is_exported && config.ansi_c.os == configt::ansi_ct::ost::OS_WIN)
    {
      dest += "__declspec(dllexport) ";
    }

    if(symbol->type.id()==ID_code &&
       to_code_type(symbol->type).get_inlined())
      dest+="inline ";
  }

  dest+=convert_rec(src.op0().type(), c_qualifierst(), declarator);

  if(src.operands().size()==2)
    dest+="="+convert(src.op1());

  dest+=';';

  return dest;
}

std::string expr2ct::convert_code_dead(
  const codet &src,
  unsigned indent)
{
  // initializer to go away
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)  + "dead " + convert(src.op0()) + ";";
}

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

  if(!src.op0().is_nil())
    dest+=convert(src.op0());
  else
    dest+=' ';
  dest+="; ";
  if(!src.op1().is_nil())
    dest+=convert(src.op1());
  dest+="; ";
  if(!src.op2().is_nil())
    dest+=convert(src.op2());

  if(src.body().is_nil())
    dest+=");\n";
  else
  {
    dest+=")\n";
    dest+=convert_code(
        src.body(),
        src.body().get_statement()==ID_block ? indent : indent+2);
  }

  return dest;
}

std::string expr2ct::convert_code_block(
  const code_blockt &src,
  unsigned indent)
{
  std::string dest=indent_str(indent);
  dest+="{\n";

  for(const auto &statement : src.statements())
  {
    if(statement.get_statement() == ID_label)
      dest += convert_code(statement, indent);
    else
      dest += convert_code(statement, indent + 2);

    dest+="\n";
  }

  dest+=indent_str(indent);
  dest+='}';

  return dest;
}

std::string expr2ct::convert_code_decl_block(
  const codet &src,
  unsigned indent)
{
  std::string dest;

  forall_operands(it, src)
  {
    dest+=convert_code(to_code(*it), indent);
    dest+="\n";
  }

  return dest;
}

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

  dest+=expr_str;
  if(dest.empty() || *dest.rbegin()!=';')
    dest+=';';

  return dest;
}

std::string expr2ct::convert_code(
  const codet &src,
  unsigned indent)
{
  static bool comment_done=false;

  if(!comment_done && !src.source_location().get_comment().empty())
  {
    comment_done=true;
    std::string dest=indent_str(indent);
    dest+="/* "+id2string(src.source_location().get_comment())+" */\n";
    dest+=convert_code(src, indent);
    comment_done=false;
    return dest;
  }

  const irep_idt &statement=src.get_statement();

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
    return convert_code_asm(to_code_asm(src), indent);

  if(statement==ID_skip)
    return indent_str(indent)+";";

  if(statement==ID_dowhile)
    return convert_code_dowhile(to_code_dowhile(src), indent);

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

  if(statement==ID_output)
    return convert_code_output(src, indent);

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

  if(statement==ID_decl_block)
    return convert_code_decl_block(src, indent);

  if(statement==ID_dead)
    return convert_code_dead(src, indent);

  if(statement==ID_assign)
    return convert_code_assign(to_code_assign(src), indent);

  if(statement=="lock")
    return convert_code_lock(src, indent);

  if(statement=="unlock")
    return convert_code_unlock(src, indent);

  if(statement==ID_atomic_begin)
    return indent_str(indent)+"__CPROVER_atomic_begin();";

  if(statement==ID_atomic_end)
    return indent_str(indent)+"__CPROVER_atomic_end();";

  if(statement==ID_function_call)
    return convert_code_function_call(to_code_function_call(src), indent);

  if(statement==ID_label)
    return convert_code_label(to_code_label(src), indent);

  if(statement==ID_switch_case)
    return convert_code_switch_case(to_code_switch_case(src), indent);

  if(statement==ID_array_set)
    return convert_code_array_set(src, indent);

  if(statement==ID_array_copy)
    return convert_code_array_copy(src, indent);

  if(statement==ID_array_replace)
    return convert_code_array_replace(src, indent);

  if(statement=="set_may" ||
     statement=="set_must")
    return
      indent_str(indent)+convert_function(src, id2string(statement), 16)+";";

  unsigned precedence;
  return convert_norep(src, precedence);
}

std::string expr2ct::convert_code_assign(
  const code_assignt &src,
  unsigned indent)
{
  std::string tmp=convert_binary(src, "=", 2, true);

  std::string dest=indent_str(indent)+tmp+";";

  return dest;
}

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
    std::string lhs_str=convert_with_precedence(src.lhs(), p);

    // TODO: ggf. Klammern je nach p
    dest+=lhs_str;
    dest+='=';
  }

  {
    unsigned p;
    std::string function_str=convert_with_precedence(src.function(), p);
    dest+=function_str;
  }

  dest+='(';

  const exprt::operandst &arguments=src.arguments();

  forall_expr(it, arguments)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=arguments.begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

std::string expr2ct::convert_code_printf(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"printf(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

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
        dest+='+';

      dest+=id2string(att[i]);
    }
  }

  dest+=");";
  return dest;
}

std::string expr2ct::convert_code_input(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"INPUT(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

std::string expr2ct::convert_code_output(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"OUTPUT(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

std::string expr2ct::convert_code_array_set(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"ARRAY_SET(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

std::string expr2ct::convert_code_array_copy(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"ARRAY_COPY(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    // TODO: ggf. Klammern je nach p
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

std::string expr2ct::convert_code_array_replace(
  const codet &src,
  unsigned indent)
{
  std::string dest=indent_str(indent)+"ARRAY_REPLACE(";

  forall_operands(it, src)
  {
    unsigned p;
    std::string arg_str=convert_with_precedence(*it, p);

    if(it!=src.operands().begin())
      dest+=", ";
    dest+=arg_str;
  }

  dest+=");";

  return dest;
}

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

std::string expr2ct::convert_code_assume(
  const codet &src,
  unsigned indent)
{
  if(src.operands().size()!=1)
  {
    unsigned precedence;
    return convert_norep(src, precedence);
  }

  return indent_str(indent)+"__CPROVER_assume("+convert(src.op0())+");";
}

std::string expr2ct::convert_code_label(
  const code_labelt &src,
  unsigned indent)
{
  std::string labels_string;

  irep_idt label=src.get_label();

  labels_string+="\n";
  labels_string+=indent_str(indent);
  labels_string+=clean_identifier(label);
  labels_string+=":\n";

  std::string tmp=convert_code(src.code(), indent+2);

  return labels_string+tmp;
}

std::string expr2ct::convert_code_switch_case(
  const code_switch_caset &src,
  unsigned indent)
{
  std::string labels_string;

  if(src.is_default())
  {
    labels_string+="\n";
    labels_string+=indent_str(indent);
    labels_string+="default:\n";
  }
  else
  {
    labels_string+="\n";
    labels_string+=indent_str(indent);
    labels_string+="case ";
    labels_string+=convert(src.case_op());
    labels_string+=":\n";
  }

  unsigned next_indent=indent;
  if(src.code().get_statement()!=ID_block &&
     src.code().get_statement()!=ID_switch_case)
    next_indent+=2;
  std::string tmp=convert_code(src.code(), next_indent);

  return labels_string+tmp;
}

std::string expr2ct::convert_code(const codet &src)
{
  return convert_code(src, 0);
}

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
  dest+='{';

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

  dest+='}';

  return dest;
}

std::string expr2ct::convert_extractbit(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest=convert_with_precedence(src.op0(), precedence);
  dest+='[';
  dest+=convert_with_precedence(src.op1(), precedence);
  dest+=']';

  return dest;
}

std::string expr2ct::convert_extractbits(
  const exprt &src,
  unsigned precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest=convert_with_precedence(src.op0(), precedence);
  dest+='[';
  dest+=convert_with_precedence(src.op1(), precedence);
  dest+=", ";
  dest+=convert_with_precedence(src.op2(), precedence);
  dest+=']';

  return dest;
}

std::string expr2ct::convert_sizeof(
  const exprt &src,
  unsigned &precedence)
{
  if(src.has_operands())
    return convert_norep(src, precedence);

  std::string dest="sizeof(";
  dest+=convert(static_cast<const typet&>(src.find(ID_type_arg)));
  dest+=')';

  return dest;
}

std::string expr2ct::convert_with_precedence(
  const exprt &src,
  unsigned &precedence)
{
  precedence=16;

  if(src.id()==ID_plus)
    return convert_multi_ary(src, "+", precedence=12, false);

  else if(src.id()==ID_minus)
    return convert_binary(src, "-", precedence=12, true);

  else if(src.id()==ID_unary_minus)
    return convert_unary(src, "-", precedence=15);

  else if(src.id()==ID_unary_plus)
    return convert_unary(src, "+", precedence=15);

  else if(src.id()==ID_floatbv_plus)
    return convert_function(src, "FLOAT+", precedence=16);

  else if(src.id()==ID_floatbv_minus)
    return convert_function(src, "FLOAT-", precedence=16);

  else if(src.id()==ID_floatbv_mult)
    return convert_function(src, "FLOAT*", precedence=16);

  else if(src.id()==ID_floatbv_div)
    return convert_function(src, "FLOAT/", precedence=16);

  else if(src.id()==ID_floatbv_rem)
    return convert_function(src, "FLOAT%", precedence=16);

  else if(src.id()==ID_floatbv_typecast)
  {
    precedence=16;
    std::string dest="FLOAT_TYPECAST(";

    unsigned p0;
    std::string tmp0=convert_with_precedence(src.op0(), p0);

    if(p0<=1)
      dest+='(';
    dest+=tmp0;
    if(p0<=1)
      dest+=')';

    const typet &to_type=ns.follow(src.type());
    dest+=", ";
    dest+=convert(to_type);
    dest+=", ";

    unsigned p1;
    std::string tmp1=convert_with_precedence(src.op1(), p1);

    if(p1<=1)
      dest+='(';
    dest+=tmp1;
    if(p1<=1)
      dest+=')';

    dest+=')';
    return dest;
  }

  else if(src.id()==ID_sign)
  {
    if(src.operands().size()==1 &&
       src.op0().type().id()==ID_floatbv)
      return convert_function(src, "signbit", precedence=16);
    else
      return convert_function(src, "SIGN", precedence=16);
  }

  else if(src.id()==ID_popcount)
  {
    if(config.ansi_c.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
      return convert_function(src, "__popcnt", precedence=16);
    else
      return convert_function(src, "__builtin_popcount", precedence=16);
  }

  else if(src.id() == ID_r_ok)
    return convert_function(src, "R_OK", precedence = 16);

  else if(src.id() == ID_w_ok)
    return convert_function(src, "W_OK", precedence = 16);

  else if(src.id()==ID_invalid_pointer)
    return convert_function(src, "INVALID-POINTER", precedence=16);

  else if(src.id()==ID_good_pointer)
    return convert_function(src, "GOOD_POINTER", precedence=16);

  else if(src.id()==ID_object_size)
    return convert_function(src, "OBJECT_SIZE", precedence=16);

  else if(src.id()=="pointer_arithmetic")
    return convert_pointer_arithmetic(src, precedence=16);

  else if(src.id()=="pointer_difference")
    return convert_pointer_difference(src, precedence=16);

  else if(src.id() == ID_null_object)
    return "NULL-object";

  else if(src.id()==ID_integer_address ||
          src.id()==ID_integer_address_object ||
          src.id()==ID_stack_object ||
          src.id()==ID_static_object)
  {
    return id2string(src.id());
  }

  else if(src.id()==ID_infinity)
    return convert_function(src, "INFINITY", precedence=16);

  else if(src.id()=="builtin-function")
    return src.get_string(ID_identifier);

  else if(src.id()==ID_pointer_object)
    return convert_function(src, "POINTER_OBJECT", precedence=16);

  else if(src.id()=="get_must")
    return convert_function(src, "__CPROVER_get_must", precedence=16);

  else if(src.id()=="get_may")
    return convert_function(src, "__CPROVER_get_may", precedence=16);

  else if(src.id()=="object_value")
    return convert_function(src, "OBJECT_VALUE", precedence=16);

  else if(src.id()==ID_array_of)
    return convert_array_of(src, precedence=16);

  else if(src.id()==ID_pointer_offset)
    return convert_function(src, "POINTER_OFFSET", precedence=16);

  else if(src.id()=="pointer_base")
    return convert_function(src, "POINTER_BASE", precedence=16);

  else if(src.id()=="pointer_cons")
    return convert_function(src, "POINTER_CONS", precedence=16);

  else if(src.id()==ID_invalid_pointer)
    return convert_function(src, "__CPROVER_invalid_pointer", precedence=16);

  else if(src.id()==ID_dynamic_object)
    return convert_function(src, "DYNAMIC_OBJECT", precedence=16);

  else if(src.id()=="is_zero_string")
    return convert_function(src, "IS_ZERO_STRING", precedence=16);

  else if(src.id()=="zero_string")
    return convert_function(src, "ZERO_STRING", precedence=16);

  else if(src.id()=="zero_string_length")
    return convert_function(src, "ZERO_STRING_LENGTH", precedence=16);

  else if(src.id()=="buffer_size")
    return convert_function(src, "BUFFER_SIZE", precedence=16);

  else if(src.id()==ID_isnan)
    return convert_function(src, "isnan", precedence=16);

  else if(src.id()==ID_isfinite)
    return convert_function(src, "isfinite", precedence=16);

  else if(src.id()==ID_isinf)
    return convert_function(src, "isinf", precedence=16);

  else if(src.id()==ID_bswap)
    return convert_function(
      src,
      "__builtin_bswap" +
        integer2string(*pointer_offset_bits(src.op0().type(), ns)),
      precedence = 16);

  else if(src.id()==ID_isnormal)
    return convert_function(src, "isnormal", precedence=16);

  else if(src.id()==ID_builtin_offsetof)
    return convert_function(src, "builtin_offsetof", precedence=16);

  else if(src.id()==ID_gcc_builtin_va_arg)
    return convert_function(src, "gcc_builtin_va_arg", precedence=16);

  else if(src.id()==ID_alignof)
    // C uses "_Alignof", C++ uses "alignof"
    return convert_function(src, "alignof", precedence=16);

  else if(has_prefix(src.id_string(), "byte_extract"))
    return convert_byte_extract(src, precedence=16);

  else if(has_prefix(src.id_string(), "byte_update"))
    return convert_byte_update(src, precedence=16);

  else if(src.id()==ID_address_of)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else if(src.op0().id()==ID_label)
      return "&&"+src.op0().get_string(ID_identifier);
    else if(src.op0().id()==ID_index &&
            to_index_expr(src.op0()).index().is_zero())
      return convert(to_index_expr(src.op0()).array());
    else if(src.type().subtype().id()==ID_code)
      return convert_unary(src, "", precedence=15);
    else
      return convert_unary(src, "&", precedence=15);
  }

  else if(src.id()==ID_dereference)
  {
    if(src.operands().size()!=1)
      return convert_norep(src, precedence);
    else if(src.type().id()==ID_code)
      return convert_unary(src, "", precedence=15);
    else if(src.op0().id()==ID_plus &&
            src.op0().operands().size()==2 &&
            ns.follow(src.op0().op0().type()).id()==ID_pointer)
    {
      // Note that index[pointer] is legal C, but we avoid it nevertheless.
      return convert(index_exprt(src.op0().op0(), src.op0().op1()));
    }
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
    return
      convert_function_application(
        to_function_application_expr(src), precedence);

  else if(src.id()==ID_side_effect)
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
      return
        convert_side_effect_expr_function_call(
          to_side_effect_expr_function_call(src), precedence);
    else if(statement == ID_allocate)
      return convert_allocate(src, precedence = 15);
    else if(statement==ID_printf)
      return convert_function(src, "printf", precedence=16);
    else if(statement==ID_nondet)
      return convert_nondet(src, precedence=16);
    else if(statement=="prob_coin")
      return convert_prob_coin(src, precedence=16);
    else if(statement=="prob_unif")
      return convert_prob_uniform(src, precedence=16);
    else if(statement==ID_statement_expression)
      return convert_statement_expression(src, precedence=15);
    else if(statement==ID_gcc_builtin_va_arg_next)
      return convert_function(src, "gcc_builtin_va_arg_next", precedence=16);
    else
      return convert_norep(src, precedence);
  }

  else if(src.id()==ID_literal)
    return convert_literal(src, precedence=16);

  else if(src.id()==ID_not)
    return convert_unary(src, "!", precedence=15);

  else if(src.id()==ID_bitnot)
    return convert_unary(src, "~", precedence=15);

  else if(src.id()==ID_mult)
    return convert_multi_ary(src, "*", precedence=13, false);

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
    return convert_function(src, "IEEE_FLOAT_EQUAL", precedence=16);

  else if(src.id()==ID_width)
    return convert_function(src, "WIDTH", precedence=16);

  else if(src.id()==ID_concatenation)
    return convert_function(src, "CONCATENATION", precedence=16);

  else if(src.id()==ID_ieee_float_notequal)
    return convert_function(src, "IEEE_FLOAT_NOTEQUAL", precedence=16);

  else if(src.id()==ID_abs)
    return convert_function(src, "abs", precedence=16);

  else if(src.id()==ID_complex_real)
    return convert_function(src, "__real__", precedence=16);

  else if(src.id()==ID_complex_imag)
    return convert_function(src, "__imag__", precedence=16);

  else if(src.id()==ID_complex)
    return convert_complex(src, precedence=16);

  else if(src.id()==ID_bitand)
    return convert_multi_ary(src, "&", precedence=8, false);

  else if(src.id()==ID_bitxor)
    return convert_multi_ary(src, "^", precedence=7, false);

  else if(src.id()==ID_bitor)
    return convert_multi_ary(src, "|", precedence=6, false);

  else if(src.id()==ID_and)
    return convert_multi_ary(src, "&&", precedence=5, false);

  else if(src.id()==ID_or)
    return convert_multi_ary(src, "||", precedence=4, false);

  else if(src.id()==ID_xor)
    return convert_multi_ary(src, "!=", precedence = 9, false);

  else if(src.id()==ID_implies)
    return convert_binary(src, "==>", precedence=3, true);

  else if(src.id()==ID_if)
    return convert_trinary(src, "?", ":", precedence=3);

  else if(src.id()==ID_forall)
    return convert_quantifier(src, "forall", precedence=2);

  else if(src.id()==ID_exists)
    return convert_quantifier(src, "exists", precedence=2);

  else if(src.id()==ID_lambda)
    return convert_quantifier(src, "LAMBDA", precedence=2);

  else if(src.id()==ID_with)
    return convert_with(src, precedence=16);

  else if(src.id()==ID_update)
    return convert_update(src, precedence=16);

  else if(src.id()==ID_member_designator)
    return precedence=16, convert_member_designator(src);

  else if(src.id()==ID_index_designator)
    return precedence=16, convert_index_designator(src);

  else if(src.id()==ID_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_nondet_symbol)
    return convert_nondet_symbol(to_nondet_symbol_expr(src), precedence);

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
    return convert_constant(to_constant_expr(src), precedence);

  else if(src.id()==ID_string_constant)
    return '"'+MetaString(src.get_string(ID_value))+'"';

  else if(src.id()==ID_struct)
    return convert_struct(src, precedence);

  else if(src.id()==ID_vector)
    return convert_vector(src, precedence);

  else if(src.id()==ID_union)
    return convert_union(src, precedence);

  else if(src.id()==ID_array)
    return convert_array(src, precedence);

  else if(src.id() == ID_array_list)
    return convert_array_list(src, precedence);

  else if(src.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(src), precedence=14);

  else if(src.id()==ID_comma)
    return convert_comma(src, precedence=1);

  else if(src.id()==ID_ptr_object)
    return "PTR_OBJECT("+id2string(src.get(ID_identifier))+")";

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

  else if(src.id()==ID_initializer_list ||
          src.id()==ID_compound_literal)
    return convert_initializer_list(src, precedence=15);

  else if(src.id()==ID_designated_initializer)
    return convert_designated_initializer(src, precedence=15);

  else if(src.id()==ID_sizeof)
    return convert_sizeof(src, precedence);

  else if(src.id()==ID_let)
    return convert_let(to_let_expr(src), precedence=16);

  else if(src.id()==ID_type)
    return convert(src.type());

  // no C language expression for internal representation
  return convert_norep(src, precedence);
}

std::string expr2ct::convert(const exprt &src)
{
  unsigned precedence;
  return convert_with_precedence(src, precedence);
}

/// Build a declaration string, which requires converting both a type and
/// putting an identifier in the syntactically correct position.
/// \param src: the type to convert
/// \param identifier: the identifier to use as the type
/// \return A C declaration of the given type with the right identifier.
std::string expr2ct::convert_with_identifier(
  const typet &src,
  const std::string &identifier)
{
  return convert_rec(src, c_qualifierst(), identifier);
}

std::string expr2c(
  const exprt &expr,
  const namespacet &ns,
  const expr2c_configurationt &configuration)
{
  std::string code;
  expr2ct expr2c(ns, configuration);
  expr2c.get_shorthands(expr);
  return expr2c.convert(expr);
}

std::string expr2c(const exprt &expr, const namespacet &ns)
{
  return expr2c(expr, ns, expr2c_configurationt::default_configuration);
}

std::string type2c(
  const typet &type,
  const namespacet &ns,
  const expr2c_configurationt &configuration)
{
  expr2ct expr2c(ns, configuration);
  // expr2c.get_shorthands(expr);
  return expr2c.convert(type);
}

std::string type2c(const typet &type, const namespacet &ns)
{
  return type2c(type, ns, expr2c_configurationt::default_configuration);
}

std::string type2c(
  const typet &type,
  const std::string &identifier,
  const namespacet &ns,
  const expr2c_configurationt &configuration)
{
  expr2ct expr2c(ns, configuration);
  return expr2c.convert_with_identifier(type, identifier);
}
