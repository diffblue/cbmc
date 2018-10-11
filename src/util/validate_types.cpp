/*******************************************************************\

Module: Validate types

Author: Daniel Poetzl

\*******************************************************************/

#include "validate_types.h"

#ifdef REPORT_UNIMPLEMENTED_TYPE_CHECKS
#include <iostream>
#endif

#include "namespace.h"
#include "std_types.h"
#include "type.h"
#include "validate.h"
#include "validate_helpers.h"

#define CALL_ON_TYPE(type_type)                                                \
  C<typet, type_type>()(type, std::forward<Args>(args)...)

template <template <typename, typename> class C, typename... Args>
void call_on_type(const typet &type, Args &&... args)
{
  if(type.id() == ID_bv)
  {
    CALL_ON_TYPE(bv_typet);
  }
  else if(type.id() == ID_unsignedbv)
  {
    CALL_ON_TYPE(unsignedbv_typet);
  }
  else if(type.id() == ID_signedbv)
  {
    CALL_ON_TYPE(signedbv_typet);
  }
  else if(type.id() == ID_fixedbv)
  {
    CALL_ON_TYPE(fixedbv_typet);
  }
  else if(type.id() == ID_floatbv)
  {
    CALL_ON_TYPE(floatbv_typet);
  }
  else if(type.id() == ID_pointer)
  {
    CALL_ON_TYPE(pointer_typet);
  }
  else if(type.id() == ID_c_bool)
  {
    CALL_ON_TYPE(c_bool_typet);
  }
  else
  {
#ifdef REPORT_UNIMPLEMENTED_TYPE_CHECKS
    std::cerr << "Unimplemented well-formedness check for type with id: "
              << type.id_string() << std::endl;
#endif

    CALL_ON_TYPE(typet);
  }
}

/// Check that the given type is well-formed (shallow checks only, i.e.,
/// subtypes are not checked)
///
/// The function determines the type `T` of the type `type` (by inspecting
/// the id() field) and then calls T::check(type, vm).
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void check_type(const typet &type, const validation_modet vm)
{
  call_on_type<call_checkt>(type, vm);
}

/// Check that the given type is well-formed, assuming that its subtypes have
/// already been checked for well-formedness.
///
/// The function determines the type `T` of the type `type` (by inspecting
/// the id() field) and then calls T::validate(type, ns, vm).
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void validate_type(
  const typet &type,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_type<call_validatet>(type, ns, vm);
}

/// Check that the given type is well-formed (full check, including checks of
/// subtypes)
///
/// The function determines the type `T` of the type `type` (by inspecting
/// the id() field) and then calls T::validate_full(type, ns, vm).
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void validate_full_type(
  const typet &type,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_type<call_validate_fullt>(type, ns, vm);
}
