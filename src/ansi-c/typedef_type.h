/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_TYPEDEF_TYPE_H
#define CPROVER_ANSI_C_TYPEDEF_TYPE_H

#include <util/type.h>

/// A typedef
class typedef_typet : public typet
{
public:
  explicit typedef_typet(const irep_idt &identifier) : typet(ID_typedef_type)
  {
    set_identifier(identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

/// Cast a generic typet to a \ref typedef_typet. This is an unchecked
/// conversion. \a type must be known to be \ref typedef_typet.
/// \param type: Source type
/// \return Object of type \ref typedef_typet
/// \ingroup gr_std_types
inline const typedef_typet &to_typedef_type(const typet &type)
{
  PRECONDITION(type.id() == ID_typedef_type);
  return static_cast<const typedef_typet &>(type);
}

/// \copydoc to_typedef_type(const typet &)
/// \ingroup gr_std_types
inline typedef_typet &to_typedef_type(typet &type)
{
  PRECONDITION(type.id() == ID_typedef_type);
  return static_cast<typedef_typet &>(type);
}

template <>
inline bool can_cast_type<typedef_typet>(const typet &type)
{
  return type.id() == ID_typedef_type;
}

#endif // CPROVER_ANSI_C_TYPEDEF_TYPE_H
