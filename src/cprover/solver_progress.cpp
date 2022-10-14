/*******************************************************************\

Module: Solver Progress Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Solver Progress Reporting

#include "solver_progress.h"

#include "console.h"

#include <iostream>

void solver_progresst::operator()(size_t current)
{
  if(verbose)
  {
  }
  else
  {
    if(first)
    {
      first = false;
    }
    else
    {
      if(consolet::is_terminal())
      {
        // up one row and clear the line
        std::cout << consolet::cursorup << consolet::cleareol;
      }
    }

    std::cout << consolet::orange << "Processing property " << (current + 1)
              << '/' << total << consolet::reset << '\n';
  }
}

void solver_progresst::finished()
{
  if(verbose)
  {
  }
  else
  {
    if(consolet::is_terminal())
    {
      if(!first)
      {
        // up one row and clear the line
        std::cout << consolet::cursorup << consolet::cleareol;
      }
    }
  }
}
