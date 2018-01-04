/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "satcheck.h"
#include <util/string2int.h>
#include <util/options.h>

// Sanity check

#ifdef SATCHECK_MINISAT1
#ifndef HAVE_MINISAT
#error "I expected to have MiniSat 1"
#endif
#endif

#ifdef SATCHECK_MINISAT2
#ifndef HAVE_MINISAT2
#error "I expected to have MiniSat 2"
#endif
#endif

satcheck_infot parse_satcheck_info(const optionst &options)
{
  satcheck_infot satcheck_info;
  if(!options.get_option("random-seed").empty())
    satcheck_info.random_seed =
      safe_string2size_t(options.get_option("random-seed"));
  if(!options.get_option("random-var-freq").empty())
    satcheck_info.random_var_freq =
      std::stod(options.get_option("random-var-freq"));
  return satcheck_info;
}
