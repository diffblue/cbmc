/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_CONE_OF_INFLUENCE_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_CONE_OF_INFLUENCE_H

#include <goto-programs/goto_program.h>

#include <util/symbol_table.h>

#include <unordered_set>

typedef std::unordered_set<exprt, irep_hash> expr_sett;

void cone_of_influence(goto_programt &program,
    expr_sett &targets,
    expr_sett &cone);

class cone_of_influencet
{
 public:
  cone_of_influencet(const goto_programt &_program,
      const symbol_tablet &symbol_table) :
    program(_program),
    ns(symbol_table)
  {
  }

  void cone_of_influence(const expr_sett &targets, expr_sett &cone);
  void cone_of_influence(const exprt &target, expr_sett &cone);

 protected:
  void cone_of_influence(const goto_programt::instructiont &i,
      const expr_sett &curr,
      expr_sett &next);
  void get_succs(goto_programt::instructionst::const_reverse_iterator rit,
      expr_sett &targets);
  void gather_rvalues(const exprt &expr, expr_sett &rvals);

  typedef std::unordered_map<unsigned int, expr_sett> cone_mapt;
  cone_mapt cone_map;

  const goto_programt &program;
  const namespacet ns;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_CONE_OF_INFLUENCE_H
