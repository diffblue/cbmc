/*******************************************************************\

Module: Elide C++ returned temporaries (guaranteed copy elision)

Author: Kiro

\*******************************************************************/

/// \file
/// Lower by-value returns of non-POD C++ class types to
/// construct-into-caller-storage, implementing N5008 [class.copy.elis]
/// and [stmt.return]/2: the operand of a return statement initializes
/// the function call's result object directly.  Without this lowering,
/// the returned object is relocated bitwise through the return-value
/// mechanism, which breaks classes whose invariants tie a member to the
/// object's own storage (e.g. the small-string optimization's
/// self-pointer) and runs the temporary's destructor after its bits
/// have been copied out (double-free in heap-owning classes).

#ifndef CPROVER_GOTO_PROGRAMS_ELIDE_CPP_RETURNED_TEMPORARIES_H
#define CPROVER_GOTO_PROGRAMS_ELIDE_CPP_RETURNED_TEMPORARIES_H

class goto_modelt;

/// Rewrite every C++ function that returns a non-POD class by value to
/// take a hidden result-pointer parameter and construct the returned
/// temporary directly into it, as compilers do for such returns
/// (Itanium ABI: sret).  Call sites pass the address of the variable
/// that would have received the return value.  Must run after function
/// pointers have been resolved to direct calls.
void elide_cpp_returned_temporaries(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_ELIDE_CPP_RETURNED_TEMPORARIES_H
