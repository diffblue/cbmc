/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <util/type.h>

#include "java_bytecode_parse_tree.h"

#ifndef CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
#define CPROVER_JAVA_BYTECODE_JAVA_UTILS_H

bool java_is_array_type(const typet &type);

/// Returns the number of JVM local variables (slots) taken by a local variable
/// that, when translated to goto, has type \p t.
unsigned java_local_variable_slots(const typet &t);

/// Returns the the number of JVM local variables (slots) used by the JVM to
/// pass, upon call, the arguments of a Java method whose type is \p t.
unsigned java_method_parameter_slots(const code_typet &t);

#endif // CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
