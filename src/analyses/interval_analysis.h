/*******************************************************************\

Module: Interval Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interval Analysis
/// Interval Analysis -- implements the functionality necessary for performing
/// abstract interpretation over interval domain for goto programs. The result
/// of the analysis is an instrumented program.

#ifndef CPROVER_ANALYSES_INTERVAL_ANALYSIS_H
#define CPROVER_ANALYSES_INTERVAL_ANALYSIS_H

class goto_modelt;

void interval_analysis(goto_modelt &);

#endif // CPROVER_ANALYSES_INTERVAL_ANALYSIS_H
