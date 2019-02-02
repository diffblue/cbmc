/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_parser.h"

#include "c_storage_spec.h"

ansi_c_parsert ansi_c_parser;

ansi_c_id_classt ansi_c_parsert::lookup(
  const irep_idt &base_name,
  irep_idt &identifier, // output
  bool tag,
  bool label)
{
  // labels and tags have a separate name space
  const irep_idt scope_name=
    tag?"tag-"+id2string(base_name):
    label?"label-"+id2string(base_name):
    base_name;

  for(scopest::const_reverse_iterator it=scopes.rbegin();
      it!=scopes.rend();
      it++)
  {
    scopet::name_mapt::const_iterator n_it=
      it->name_map.find(scope_name);

    if(n_it!=it->name_map.end())
    {
      identifier=n_it->second.prefixed_name;
      return n_it->second.id_class;
    }
  }

  // Not found.
  // If it's a tag, we will add to current scope.
  if(tag)
  {
    ansi_c_identifiert &i=
      current_scope().name_map[scope_name];
    i.id_class=ansi_c_id_classt::ANSI_C_TAG;
    i.prefixed_name=current_scope().prefix+id2string(scope_name);
    i.base_name=base_name;
    identifier=i.prefixed_name;
    return ansi_c_id_classt::ANSI_C_TAG;
  }

  identifier=base_name;
  return ansi_c_id_classt::ANSI_C_UNKNOWN;
}

void ansi_c_parsert::add_tag_with_body(irept &tag)
{
  const std::string scope_name=
    "tag-"+tag.get_string(ID_C_base_name);

  irep_idt prefixed_name=current_scope().prefix+scope_name;

  if(prefixed_name!=tag.get(ID_identifier))
  {
    // re-defined in a deeper scope
    ansi_c_identifiert &identifier=
      current_scope().name_map[scope_name];
    identifier.id_class=ansi_c_id_classt::ANSI_C_TAG;
    identifier.prefixed_name=prefixed_name;
    tag.set(ID_identifier, prefixed_name);
  }
}

extern char *yyansi_ctext;

int yyansi_cerror(const std::string &error)
{
  ansi_c_parser.parse_error(error, yyansi_ctext);
  return 0;
}

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
  if(current_scope().prefix.empty())
    ansi_c_declaration.set_is_global(true);

  // abstract?
  if(!base_name.empty())
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

    ansi_c_id_classt id_class=is_typedef?
      ansi_c_id_classt::ANSI_C_TYPEDEF:
      ansi_c_id_classt::ANSI_C_SYMBOL;

    scopet &scope=
      force_root_scope?root_scope():current_scope();

    // set the final name
    irep_idt prefixed_name=force_root_scope?
             base_name:
             current_scope().prefix+id2string(base_name);
    new_declarator.set_name(prefixed_name);

    // add to scope
    ansi_c_identifiert &identifier=scope.name_map[base_name];
    identifier.id_class=id_class;
    identifier.prefixed_name=prefixed_name;

    if(force_root_scope)
      current_scope().name_map[base_name] = identifier;
  }

  ansi_c_declaration.declarators().push_back(new_declarator);
}

ansi_c_id_classt ansi_c_parsert::get_class(const typet &type)
{
  if(type.id()==ID_typedef)
    return ansi_c_id_classt::ANSI_C_TYPEDEF;
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_c_enum)
    return ansi_c_id_classt::ANSI_C_TAG;
  else if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      if(get_class(*it)==ansi_c_id_classt::ANSI_C_TYPEDEF)
        return ansi_c_id_classt::ANSI_C_TYPEDEF;
  }
  else if(type.has_subtype())
    return get_class(type.subtype());

  return ansi_c_id_classt::ANSI_C_SYMBOL;
}
