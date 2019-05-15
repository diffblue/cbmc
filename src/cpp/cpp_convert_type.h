/*******************************************************************\

Module: C++ Language Conversion

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Conversion

#ifndef CPROVER_CPP_CPP_CONVERT_TYPE_H
#define CPROVER_CPP_CPP_CONVERT_TYPE_H

class message_handlert;
class typet;

void cpp_convert_plain_type(typet &, message_handlert &);

void cpp_convert_auto(typet &dest, const typet &src, message_handlert &);

#endif // CPROVER_CPP_CPP_CONVERT_TYPE_H
