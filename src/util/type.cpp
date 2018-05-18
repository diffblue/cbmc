/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "type.h"
#include "std_types.h"
#include "namespace.h"

void typet::copy_to_subtypes(const typet &type)
{
  subtypes().push_back(type);
}

void typet::move_to_subtypes(typet &type)
{
  subtypest &sub=subtypes();
  sub.push_back(static_cast<const typet &>(get_nil_irep()));
  sub.back().swap(type);
}

bool is_number(const typet &type)
{
  const irep_idt &id=type.id();
  return id==ID_rational ||
         id==ID_real ||
         id==ID_integer ||
         id==ID_natural ||
         id==ID_complex ||
         id==ID_unsignedbv ||
         id==ID_signedbv ||
         id==ID_floatbv ||
         id==ID_fixedbv;
}

/// Identify if a given type is constant itself or
/// contains constant components. Examples include:
///  - const int a;
///  - struct contains_constant_pointer {  int x; int * const p; };
///  - const int b[3];
/// \param type The type we want to query constness of.
/// \param ns The namespace, needed for resolution of symbols.
/// \return Whether passed in type is const or not.
bool is_constant_or_has_constant_components(
  const typet &type, const namespacet &ns)
{
  // Helper function to avoid the code duplication in the branches
  // below.
  const auto has_constant_components =
    [&ns](const typet &subtype) -> bool
    {
      if(subtype.id() == ID_struct || subtype.id() == ID_union)
      {
        const auto &struct_union_type = to_struct_union_type(subtype);
        for(const auto &component : struct_union_type.components())
        {
          if(is_constant_or_has_constant_components(component.type(), ns))
            return true;
        }
      }
      return false;
    };

  // There are 4 possibilities the code below is handling.
  // The possibilities are enumerated as comments, to show
  // what each code is supposed to be handling. For more
  // comprehensive test case for this, take a look at
  // regression/cbmc/no_nondet_static/main.c

  // const int a;
  if(type.get_bool(ID_C_constant))
    return true;

  // This is a termination condition to break the recursion
  // for recursive types such as the following:
  // struct list { const int datum; struct list * next; };
  // NOTE: the difference between this condition and the previous
  // one is that this one always returns.
  if(type.id()==ID_pointer)
    return type.get_bool(ID_C_constant);

  // When we have a case like the following, we don't immediately
  // see the struct t. Instead, we only get to see symbol t1, which
  // we have to use the namespace to resolve to its definition:
  // struct t { const int a; };
  // struct t t1;
  if(type.id() == ID_symbol_type)
  {
    const auto &resolved_type = ns.follow(type);
    return has_constant_components(resolved_type);
  }

  // In a case like this, where we see an array (b[3] here), we know that
  // the array contains subtypes. We get the first one, and
  // then resolve it to its  definition through the usage of the namespace.
  // struct contains_constant_pointer { int x; int * const p; };
  // struct contains_constant_pointer b[3] = { {23, &y}, {23, &y}, {23, &y} };
  if(type.has_subtype())
  {
    const auto &subtype = type.subtype();
    return is_constant_or_has_constant_components(subtype, ns);
  }

  return false;
}
