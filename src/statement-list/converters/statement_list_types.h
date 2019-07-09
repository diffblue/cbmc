/*******************************************************************\

Module: Statement List Type Helper

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Type Helper

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_STATEMENT_LIST_TYPES_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_STATEMENT_LIST_TYPES_H

#define STL_INT_WIDTH 16u
#define STL_DINT_WIDTH 32u

/// Creates a new type that resembles the 'Int' type of the Siemens PLC
/// languages.
/// \return The type object for 'Int'.
class signedbv_typet get_int_type();
/// Creates a new type that resembles the 'DInt' type of the Siemens PLC
/// languages.
/// \return The type object for 'DInt'.
class signedbv_typet get_dint_type();
/// Creates a new type that resembles the 'Real' type of the Siemens PLC
/// languages.
/// \return The type object for 'Real'.
class floatbv_typet get_real_type();
/// Creates a new type that resembles the 'Bool' type of the Siemens PLC
/// languages.
/// \return The type object for 'Bool'.
class bool_typet get_bool_type();

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_STATEMENT_LIST_TYPES_H
