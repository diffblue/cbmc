/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_CEGIS_LIBRARY_H_
#define CEGIS_CEGIS_LIBRARY_H_

/**
 * @brief
 *
 * @details
 *
 * @param symbol_table
 * @param goto_functions
 * @param msg
 */
void add_cegis_library(class symbol_tablet &symbol_table,
    class goto_functionst &goto_functions, class ui_message_handlert &msg);

#endif /* CEGIS_CEGIS_LIBRARY_H_ */
