/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "ansi_c_parser.h"
#include "c_storage_spec.h"

ansi_c_parsert ansi_c_parser;

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

Function: ansi_c_parsert::add_tag_with_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_parsert::add_tag_with_body(irept &tag)
{
  const std::string scope_name=
    "tag-"+tag.get_string(ID_C_base_name);

  irep_idt identifier=current_scope().prefix+scope_name;
  
  if(identifier!=tag.get(ID_identifier))
  {
    // re-defined in a deeper scope
    current_scope().name_map[scope_name].id_class=ANSI_C_TAG;
    tag.set(ID_identifier, identifier);
  }
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
  bool is_parameter=ansi_c_declaration.get_is_parameter();
  
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
    c_storage_spect c_storage_spec(ansi_c_declaration.type());
    bool is_typedef=c_storage_spec.is_typedef;
    bool is_extern=c_storage_spec.is_extern;

    bool force_root_scope=false;
  
    // Functions always go into global scope, unless
    // declared as a parameter or are typedefs.
    if(new_declarator.type().id()==ID_code &&
       !is_parameter &&
       !is_typedef)
      force_root_scope=true;
    
    // variables marked as 'extern' always go into global scope
    if(is_extern)
      force_root_scope=true;

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
