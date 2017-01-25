/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/mp_arith.h>

#include <cegis/instrument/literals.h>
#include <cegis/invariant/meta/meta_variable_names.h>

std::string get_Ax()
{
  return CEGIS_PREFIX "A_x";
}

namespace
{
const char GUARD_PREFIX[]=CEGIS_PREFIX "G";
const char STATE_BEFORE_LOOP[]="x";
}

std::string get_Gx(const size_t loop_id)
{
  std::string result(GUARD_PREFIX);
  result+=integer2string(loop_id);
  return result+=STATE_BEFORE_LOOP;
}

std::string get_tmp(const size_t id)
{
  std::string result(CEGIS_TMP_PREFIX);
  return result+=integer2string(id);
}
