/*******************************************************************\

 Module: Find User Entry Point

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#ifndef CPROVER_ANALYSES_FIND_USER_ENTRY_POINT_H
#define CPROVER_ANALYSES_FIND_USER_ENTRY_POINT_H

#include <util/symbol_table.h>
#include <goto-programs/goto_functions.h>

const irep_idt get_entry_function_id(const goto_functionst &goto_functions);

#endif // CPROVER_ANALYSES_FIND_USER_ENTRY_POINT_H
