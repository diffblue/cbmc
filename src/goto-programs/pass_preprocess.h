/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_PASS_PREPROCESS_H
#define CPROVER_PASS_PREPROCESS_H

#include <goto-programs/goto_model.h>


exprt replace_string_literals(symbol_tablet &, goto_functionst &,const exprt & );
void pass_preprocess(symbol_tablet &, goto_functionst &);

#endif
