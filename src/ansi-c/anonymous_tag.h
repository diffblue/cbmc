/*******************************************************************\

Module: Naming of anonymous struct and union tags

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Naming of anonymous struct and union tags

#ifndef CPROVER_ANSI_C_ANONYMOUS_TAG_H
#define CPROVER_ANSI_C_ANONYMOUS_TAG_H

#include <util/invariant.h>
#include <util/irep.h>
#include <util/prefix.h>

#include <string>

/// The C front-end gives an anonymous struct or union type a tag of its own,
/// named after the type (see type2name): two anonymous types with the same
/// structure get the same tag.
struct anonymous_tag_namet
{
  irep_idt identifier;
  irep_idt base_name;
};

/// The identifier and base name of the tag of an anonymous struct or union
/// type.
/// \param typestr: the result of type2name for the type
inline anonymous_tag_namet anonymous_tag_name(const std::string &typestr)
{
  return {"tag-#anon#" + typestr, "#anon#" + typestr};
}

/// True if \p identifier is the identifier of the tag of an anonymous struct
/// or union type, as returned by anonymous_tag_name.
inline bool is_anonymous_tag(const irep_idt &identifier)
{
  return has_prefix(id2string(identifier), "tag-#anon#");
}

/// The base name of the tag of an anonymous struct or union type with
/// identifier \p identifier, as returned by anonymous_tag_name.
inline irep_idt anonymous_tag_base_name(const irep_idt &identifier)
{
  PRECONDITION(is_anonymous_tag(identifier));
  return id2string(identifier).substr(std::string{"tag-"}.size());
}

#endif // CPROVER_ANSI_C_ANONYMOUS_TAG_H
