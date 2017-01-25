/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/mp_arith.h>

#include <cegis/instrument/literals.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>

namespace
{
const char INVARIANT_PREFIX[]=DANGER_PREFIX"D";
const char SEP='_';
const char INITIAL_STATE[]="x0";
}

std::string get_Dx0()
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

std::string get_Dx(const size_t loop_id)
{
  return build_var_name(INVARIANT_PREFIX, loop_id, STATE_BEFORE_LOOP);
}

namespace
{
const char STATE_AFTER_LOOP[]="x" CEGIS_PRIME_SUFFIX;
}

std::string get_Dx_prime(const size_t loop_id)
{
  return build_var_name(INVARIANT_PREFIX, loop_id, STATE_AFTER_LOOP);
}

namespace
{
std::string build_var_name(const char * const prefix, const size_t loop_id,
    const char * const state, const size_t result_id)
{
  std::string result(prefix);
  result+=integer2string(loop_id);
  result+=SEP;
  result+=state;
  result+=SEP;
  return result+=integer2string(result_id);
}

const char RANKING_PREFIX[]=DANGER_PREFIX"R";
}

std::string get_Rx(const size_t loop_id, const size_t result_id)
{
  return build_var_name(RANKING_PREFIX, loop_id, STATE_BEFORE_LOOP, result_id);
}

std::string get_Rx_prime(const size_t loop_id, const size_t result_id)
{
  return build_var_name(RANKING_PREFIX, loop_id, STATE_AFTER_LOOP, result_id);
}

namespace
{
const char SKOLEM_PREFIX[]=DANGER_PREFIX"S";
}

std::string get_Sx(const size_t loop_id, const size_t result_id)
{
  return build_var_name(SKOLEM_PREFIX, loop_id, STATE_BEFORE_LOOP, result_id);
}
