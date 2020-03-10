/*******************************************************************\

Module: Get goto model

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_GET_GOTO_MODEL_FROM_C_H
#define CPROVER_TESTING_UTILS_GET_GOTO_MODEL_FROM_C_H

#include <goto-programs/goto_model.h>

#include <iosfwd>

/// Convert C program to a goto model
///
/// \param code: string giving the C program
/// \return goto model
goto_modelt get_goto_model_from_c(const std::string &code);

/// Convert C program to a goto model
///
/// \param in: input stream to read a C program from
/// \return goto model
goto_modelt get_goto_model_from_c(const std::istream &in);

#endif /* CPROVER_TESTING_UTILS_GET_GOTO_MODEL_FROM_C_H_ */
