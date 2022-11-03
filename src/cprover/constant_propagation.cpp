/*******************************************************************\

Module: Constant Propagation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Constant Propagation

#include "constant_propagation.h"

#include <util/format_expr.h>

#include <iostream>

#include <unordered_map>

void constant_propagation(std::vector<exprt> &constraints)
{
  for(auto &c : constraints)
  {
    std::cout << "C: " << format(c) << "\n";
  }

  // map from addresses to values
  std::unordered_map<exprt, exprt> constants;

  // iterate until saturation

}
