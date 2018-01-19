/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: November 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "json_goto_trace.h"
/// Produce a json representation of a trace.
/// \param ns: a namespace
  jsont &dest,

        DATA_INVARIANT(
          step.full_lhs.is_not_nil(),
            void operator()(exprt &expr) override
            {
              if(expr.id() == ID_symbol)
              {
        full_lhs_string=from_expr(ns, identifier, simplified);
          full_lhs_value = json(step.full_lhs_value, ns);
            json_values.push_back(json(arg, ns, mode));
            json_values.push_back(json(arg, ns, mode));
