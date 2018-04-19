/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_SCOPE_H
#define CPROVER_ANSI_C_ANSI_C_SCOPE_H

#include <util/irep.h>

#include <unordered_map>

enum class ansi_c_id_classt
{
  ANSI_C_UNKNOWN,
  ANSI_C_SYMBOL,
  ANSI_C_TYPEDEF,
  ANSI_C_TAG,
  ANSI_C_LOCAL_LABEL
};

std::ostream &operator<<(std::ostream &os, ansi_c_id_classt c);

class ansi_c_identifiert
{
public:
  ansi_c_id_classt id_class;
  irep_idt base_name, prefixed_name;

  ansi_c_identifiert():id_class(ansi_c_id_classt::ANSI_C_UNKNOWN)
  {
  }
};

class ansi_c_scopet
{
public:
  // This maps "scope names" (tag-X, label-X, X) to
  // ansi_c_identifiert.
  typedef std::unordered_map<irep_idt, ansi_c_identifiert> name_mapt;
  name_mapt name_map;

  std::string prefix;

  // We remember the last declarator for the benefit
  // of function argument scoping.
  irep_idt last_declarator;

  // for(;;) and { } scopes are numbered
  unsigned compound_counter;
  unsigned anon_counter;

  ansi_c_scopet():compound_counter(0), anon_counter(0) { }

  void swap(ansi_c_scopet &scope)
  {
    name_map.swap(scope.name_map);
    prefix.swap(scope.prefix);
    last_declarator.swap(scope.last_declarator);
    std::swap(compound_counter, scope.compound_counter);
  }

  void print(std::ostream &out) const;
};

#endif // CPROVER_ANSI_C_ANSI_C_SCOPE_H
