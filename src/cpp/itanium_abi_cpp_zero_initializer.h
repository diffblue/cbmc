/*******************************************************************\

Module: C++ Language Type Checking

Author: Kiro

\*******************************************************************/

/// \file
/// Zero-initialization and null member pointer values of the Itanium C++ ABI

#ifndef CPROVER_CPP_ITANIUM_ABI_CPP_ZERO_INITIALIZER_H
#define CPROVER_CPP_ITANIUM_ABI_CPP_ZERO_INITIALIZER_H

#include <util/expr.h>
#include <util/mp_arith.h>

#include <optional>

/// The Itanium C++ ABI (section 2.3) represents a pointer to data member by
/// the member's offset in its class and the null member pointer value by -1.
/// A pointer to data member is a value of pointer type in the goto program,
/// and the back end's pointer encoding does not yet handle arbitrary
/// integers converted to pointers consistently (`(int *)-1' compares unequal
/// to itself when formed in two ways; an integer-derived pointer added to an
/// object address fails the bounds check).  Until that is fixed, the front
/// end uses a WORKAROUND by default: the offset plus one, with the null
/// member pointer value being the null pointer.  The two encodings differ
/// only in the object representation (observable through memcpy or
/// bit_cast).  Define CPROVER_CPP_ITANIUM_DATA_MEMBER_POINTER_NULL to use the
/// exact Itanium encoding.
#ifdef CPROVER_CPP_ITANIUM_DATA_MEMBER_POINTER_NULL
#  define CPROVER_CPP_DATA_MEMBER_POINTER_BIAS 0
#else
#  define CPROVER_CPP_DATA_MEMBER_POINTER_BIAS 1
#endif

/// What is added to a data member's offset to form its pointer to member.
inline mp_integer data_member_pointer_bias()
{
  return CPROVER_CPP_DATA_MEMBER_POINTER_BIAS;
}

class namespacet;
class source_locationt;

/// Whether \p type is a pointer to DATA member ("pointer to member of C of
/// type T" with T an object type, N5008 [basic.compound]/1.8).
bool is_pointer_to_data_member_type(const typet &type);

/// The null member pointer value ([conv.mem]/1) of the pointer to data member
/// type \p type: -1, as the Itanium C++ ABI (section 2.3) represents it, or
/// the null pointer in the default workaround encoding (see above); a
/// non-null pointer to data member is the member's offset in its class plus
/// data_member_pointer_bias().
exprt null_pointer_to_data_member(const typet &type);

/// Whether the type contains a pointer to data member (as a member, base,
/// array element, or the type itself), so that zero-initializing it differs
/// from filling it with zero bytes.
bool contains_pointer_to_data_member(const typet &type, const namespacet &ns);

/// N5008 [dcl.init.general]/6: zero-initialization.  As ::zero_initializer,
/// except that a pointer to data member is initialized with the null member
/// pointer value -- "the value obtained by converting the integer literal 0
/// to T" ([dcl.init.general]/6.1) -- which in the Itanium C++ ABI is -1, not
/// all-bits-zero (in the default workaround encoding the two coincide).
std::optional<exprt> itanium_abi_cpp_zero_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns);

/// Replace, within \p expr, each null pointer constant of a pointer to data
/// member type by null_pointer_to_data_member (used after the generic
/// zero-initializer and wherever a value was built from it).
void fix_null_pointers_to_data_members(exprt &expr);

#endif // CPROVER_CPP_ITANIUM_ABI_CPP_ZERO_INITIALIZER_H
