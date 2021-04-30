/*******************************************************************\

Module: Invariant helper utilities

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Invariant helper utilities

#include "invariant_utils.h"

#include "irep.h"

std::string pretty_print_invariant_with_irep(
  const irept &problem_node,
  const std::string &description)
{
  if(problem_node.is_nil())
    return description;
  else
  {
    std::string ret=description;
    ret+="\nProblem irep:\n";
    ret+=problem_node.pretty(0,0);
    return ret;
  }
}
