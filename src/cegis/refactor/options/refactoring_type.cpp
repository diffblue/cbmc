/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cassert>

#include <util/options.h>

#include <cegis/options/parameters.h>
#include <cegis/refactor/options/refactoring_type.h>

refactoring_typet get_refactoring_type(const class optionst &options)
{
  if (options.get_bool_option(CEGIS_NULL_OBJECT_REFACTOR))
    return refactoring_typet::NULL_OBJECT;
  assert(!"Invalid refactoring type selected.");
}
