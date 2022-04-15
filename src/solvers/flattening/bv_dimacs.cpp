/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#include "bv_dimacs.h"

#include <solvers/sat/dimacs_cnf.h>

bv_dimacst::bv_dimacst(
  const namespacet &_ns,
  dimacs_cnft &_prop,
  message_handlert &message_handler,
  std::ostream &_out)
  : bv_pointerst(_ns, _prop, message_handler), out(_out), dimacs_cnf_prop(_prop)
{
}

void bv_dimacst::write_dimacs()
{
  dimacs_cnf_prop.write_dimacs_cnf(out);

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
  for(const auto &m : get_map().get_mapping())
  {
    const auto &literal_map = m.second.literal_map;

    if(literal_map.empty())
      continue;

    out << "c " << m.first;

    for(const auto &lit : literal_map)
    {
      out << ' ';

      if(lit.is_constant())
        out << (lit.is_true() ? "TRUE" : "FALSE");
      else
        out << lit.dimacs();
    }

    out << "\n";
  }
}
