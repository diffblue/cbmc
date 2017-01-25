/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/mp_arith.h>

#include <cegis/instrument/literals.h>
#include <cegis/safety/meta/meta_variable_names.h>

namespace
{
const char INVARIANT_PREFIX[]=CEGIS_PREFIX"I";
const char SEP='_';
const char INITIAL_STATE[]="x0";
}

std::string get_Ix0()
{
  std::string result(INVARIANT_PREFIX);
  result+=SEP;
  return result+=INITIAL_STATE;
}

namespace
{
std::string build_var_name(const char * const prefix, const size_t loop_id,
    const char * const state)
{
  std::string result(prefix);
  result+=integer2string(loop_id);
  result+=SEP;
  return result+=state;
}

const char STATE_BEFORE_LOOP[]="x";
}

std::string get_Ix(const size_t loop_id)
{
  return build_var_name(INVARIANT_PREFIX, loop_id, STATE_BEFORE_LOOP);
}

namespace
{
const char STATE_AFTER_LOOP[]="x" CEGIS_PRIME_SUFFIX;
}

std::string get_Ix_prime(const size_t loop_id)
{
  return build_var_name(INVARIANT_PREFIX, loop_id, STATE_AFTER_LOOP);
}
