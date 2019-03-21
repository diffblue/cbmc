/*******************************************************************\

Module: Loop shrinking

Author: Zhixing Xu, zhixingx@princeton.edu

\*******************************************************************/

/// \file
/// Loop shrinking. Based on "Property Checking Array Programs Using
/// Loop Shrinking" by Shrawan Kumar, Amitabha Sanyal, Venkatesh R and Punit
/// Shah, TACAS 2018.

#include <map>
#include <set>
#include <string>

#include <util/irep.h>

#ifndef CPROVER_GOTO_INSTRUMENT_ABSTRACT_LOOPS_H
#define CPROVER_GOTO_INSTRUMENT_ABSTRACT_LOOPS_H

class goto_modelt;

typedef std::set<unsigned> loop_idst;
typedef std::map<irep_idt, loop_idst> loop_mapt;

void abstract_loops(goto_modelt &goto_model, const loop_mapt &target_loop_map);

/// Parse target loops in string format.
/// \param inputset: input of loops to abstract in string format
/// \param [out] target_loop_map: a map from function name to loop number
/// \return return false if parse succeeds
bool parse_absloopset(const std::string &inputset, loop_mapt &target_loop_map);

// clang-format off
#define OPT_ABSTRACT_LOOPS \
  "(abstract-loops)(abstractset):"

#define HELP_ABSTRACT_LOOPS \
  /* NOLINTNEXTLINE(whitespace/line_length) */ \
  " --abstract-loops             shrink loop based on assertion dependency (experimental)\n" \
  " --abstractset L,...          only shrink loop L,...\n"
// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_ABSTRACT_LOOPS_H
