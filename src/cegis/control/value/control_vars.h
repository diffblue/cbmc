/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_CONTROL_VARS_H_
#define CEGIS_CONTROL_VARS_H_

#define CEGIS_CONTROL_SOLUTION_VAR_NAME "controller"
#define __CEGIS_ALTERNATIVE_MEMBER_NAMES
#ifndef __CEGIS_ALTERNATIVE_MEMBER_NAMES
#define CEGIS_CONTROL_A_MEMBER_NAME "a"
#define CEGIS_CONTROL_B_MEMBER_NAME "b"
#define CEGIS_CONTROL_A_SIZE_MEMBER_NAME "a_size"
#define CEGIS_CONTROL_B_SIZE_MEMBER_NAME "b_size"
#else
#define CEGIS_CONTROL_A_MEMBER_NAME "den"
#define CEGIS_CONTROL_B_MEMBER_NAME "num"
#define CEGIS_CONTROL_A_SIZE_MEMBER_NAME "den_size"
#define CEGIS_CONTROL_B_SIZE_MEMBER_NAME "num_size"
#endif

#endif /* CEGIS_CONTROL_VARS_H_ */
