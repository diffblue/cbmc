/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
#define CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include <util/std_types.h>

class namespacet;

class select_pointer_typet
{
public:
  virtual ~select_pointer_typet()=default;
  virtual pointer_typet convert_pointer_type(
    const pointer_typet &pointer_type) const;
};

#endif // CPROVER_JAVA_BYTECODE_SELECT_POINTER_TYPE_H
