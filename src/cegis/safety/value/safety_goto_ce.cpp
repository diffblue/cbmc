/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/safety/value/safety_goto_ce.h>

bool safety_goto_cet::operator ==(const safety_goto_cet &other) const
{
  return x0 == other.x0 && x == other.x;
}
