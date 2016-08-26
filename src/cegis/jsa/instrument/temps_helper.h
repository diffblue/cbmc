/*******************************************************************

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_JSA_TEMPS_HELPER_H_
#define CEGIS_JSA_TEMPS_HELPER_H_

#include <goto-programs/goto_program.h>

/**
 * @brief
 *
 * @details
 *
 * @param prog
 */
goto_programt::targett zero_jsa_temps(
    class jsa_programt &prog,
    goto_programt::targett pos);

#endif /* CEGIS_JSA_TEMPS_HELPER_H_ */
