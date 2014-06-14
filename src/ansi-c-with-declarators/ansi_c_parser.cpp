/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "ansi_c_parser.h"

ansi_c_parsert ansi_c_parser;

/*******************************************************************\

Function: ansi_c_parsert::scopet::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parsert::scopet::print(std::ostream &out) const
{
  out << "Prefix: " << prefix << std::endl;

  for(scopet::name_mapt::const_iterator n_it=name_map.begin();
      n_it!=name_map.end();
      n_it++)
  {
    out << "  ID: " << n_it->first
        << " CLASS: " << n_it->second.id_class
        << std::endl;
  }
}

/*******************************************************************\

Function: ansi_c_parsert::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ansi_c_id_classt ansi_c_parsert::lookup(
  std::string &name,
  bool tag,
  bool label)
{
  // labels and tags have a separate name space
  const std::string scope_name=
    tag?"tag-"+name:
    label?"label-"+name:
    name;
  
  for(scopest::const_reverse_iterator it=scopes.rbegin();
      it!=scopes.rend();
      it++)
  {
    scopet::name_mapt::const_iterator n_it=
      it->name_map.find(scope_name);

    if(n_it!=it->name_map.end())
    {
      name=it->prefix+scope_name;
      return n_it->second.id_class;
    }
  }
  
  // Not found.
  // If it's a tag, we will add to current scope.
  if(tag)
  {
    current_scope().name_map[scope_name].id_class=ANSI_C_TAG;
    name=current_scope().prefix+scope_name;
    return ANSI_C_TAG;
  }

  return ANSI_C_UNKNOWN;
}

/*******************************************************************\

Function: yyansi_cerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern char *yyansi_ctext;

int yyansi_cerror(const std::string &error)
{
  ansi_c_parser.parse_error(error, yyansi_ctext);
  return 0;
}

/*******************************************************************\

Function: ansi_c_parsert::add_declarator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parsert::add_declarator(
  exprt &declaration,
  irept &declarator)
{
  assert(declarator.is_not_nil());
  ansi_c_declarationt &ansi_c_declaration=
    to_ansi_c_declaration(declaration);
  
  ansi_c_declaratort new_declarator;
  new_declarator.build(declarator);

  irep_idt base_name=new_declarator.get_base_name();
  
  bool is_member=ansi_c_declaration.get_is_member();
  
  if(is_member)
  {
    // we don't put them into a struct scope (unlike C++)
    new_declarator.set_name(base_name);
    ansi_c_declaration.declarators().push_back(new_declarator);
    return; // done
  }
  
  // global?
  if(current_scope().prefix=="")
    ansi_c_declaration.set_is_global(true);

  // abstract?
  if(base_name!="")
  {
    bool is_typedef=
      ansi_c_declarationt::is_a_typedef(ansi_c_declaration.type());

    bool force_root_scope=false;
  
    if(new_declarator.type().id()==ID_code)
    {
      // functions always go into global scope
      force_root_scope=true;
    }

    ansi_c_id_classt id_class=
      is_typedef?ANSI_C_TYPEDEF:ANSI_C_SYMBOL;

    scopet &scope=
      force_root_scope?root_scope():current_scope();

    // add to scope  
    scope.name_map[base_name].id_class=id_class;

    // set the final name    
    irep_idt name=force_root_scope?
             base_name:
             current_scope().prefix+id2string(base_name);
    new_declarator.set_name(name);
  }
  
  ansi_c_declaration.declarators().push_back(new_declarator);

  #if 0
  // Visual Studio has global-scope tags  
  bool is_global=current_scope().prefix=="" ||
                 (mode==MSC && decl_type==TAG);

  ansi_c_id_classt id_class=get_class(final_type);
  
  const std::string scope_name=
    decl_type==TAG?"tag-"+base_name:base_name;
    
  if(decl_type==TAG)
    final_type.set(ID_tag, base_name);

  std::string name;

  if(base_name!="")
  {
    bool force_root_scope=false;
  
    if(mode==MSC && decl_type==TAG)
    {
      // MSC always puts tags into global scope
      force_root_scope=true;
    }
    else if(final_type.id()==ID_code && decl_type!=PARAMETER)
    {
      // functions always go into global scope,
      // unless it's a parameter
      force_root_scope=true;
    }

    name=force_root_scope?
         scope_name:
         current_scope().prefix+scope_name;

    if(decl_type!=MEMBER)
    {
      // the following is bad!
      scopet &scope=
        force_root_scope?root_scope():current_scope();

      // see if already in scope
      scopet::name_mapt::const_iterator n_it=
        scope.name_map.find(scope_name);
    
      if(n_it==scope.name_map.end())
      {
        // add to scope  
        scope.name_map[scope_name].id_class=id_class;
      }
    }
  }

  // create dest
  ansi_c_declarationt declaration;

  declaration.type().swap(final_type);
  declaration.set_base_name(base_name);
  declaration.set_name(name);
  declaration.location()=identifier.location();
  declaration.value().make_nil();
  declaration.set_is_type(decl_type==TAG || id_class==ANSI_C_TYPEDEF);
  declaration.set_is_typedef(id_class==ANSI_C_TYPEDEF);
  declaration.set_is_global(is_global);

  dest.swap(declaration);
  #endif
}

/*******************************************************************\

Function: ansi_c_parsert::get_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
 
ansi_c_id_classt ansi_c_parsert::get_class(const typet &type)
{
  if(type.id()==ID_typedef)
    return ANSI_C_TYPEDEF;
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_c_enum)
    return ANSI_C_TAG;
  else if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      if(get_class(*it)==ANSI_C_TYPEDEF)
        return ANSI_C_TYPEDEF;
  }
  else if(type.has_subtype())
    return get_class(type.subtype());

  return ANSI_C_SYMBOL;
}
