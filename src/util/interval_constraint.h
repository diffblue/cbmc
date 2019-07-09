/*******************************************************************\

Module: Interval constraint

Author: Jeannie Moulton

\*******************************************************************/

#ifndef CPROVER_UTIL_INTERVAL_CONSTRAINT_H
#define CPROVER_UTIL_INTERVAL_CONSTRAINT_H

#include "integer_interval.h"

class exprt;

/// Given an exprt and an integer interval return an exprt that represents
/// restricting the expression to the range in the interval (inclusive).
exprt interval_constraint(const exprt &expr, const integer_intervalt &interval);

#endif // CPROVER_UTIL_INTERVAL_CONSTRAINT_H
