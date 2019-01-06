/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#include "bv_dimacs.h"

#include <fstream>
#include <iostream>

#include <solvers/sat/dimacs_cnf.h>

bool bv_dimacst::write_dimacs()
{
  if(filename.empty() || filename == "-")
    return write_dimacs(std::cout);

  std::ofstream out(filename);

  if(!out)
  {
    error() << "failed to open " << filename << eom;
    return false;
  }

  return write_dimacs(out);
}

bool bv_dimacst::write_dimacs(std::ostream &out)
{
  dynamic_cast<dimacs_cnft &>(prop).write_dimacs_cnf(out);

  // we dump the mapping variable<->literals
  for(const auto &s : get_symbols())
  {
    if(s.second.is_constant())
      out << "c " << s.first << " " << (s.second.is_true() ? "TRUE" : "FALSE")
          << "\n";
    else
      out << "c " << s.first << " " << s.second.dimacs() << "\n";
  }

  // dump mapping for selected bit-vectors
  for(const auto &m : get_map().mapping)
  {
    const boolbv_mapt::literal_mapt &literal_map = m.second.literal_map;

    if(literal_map.empty())
      continue;

    out << "c " << m.first;

    for(const auto &lit : literal_map)
      if(!lit.is_set)
        out << " "
            << "?";
      else if(lit.l.is_constant())
        out << " " << (lit.l.is_true() ? "TRUE" : "FALSE");
      else
        out << " " << lit.l.dimacs();

    out << "\n";
  }

  return false;
}
