/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <solvers/sat/dimacs_cnf.h>

#include "cbmc_dimacs.h"

/*******************************************************************\

Function: cbmc_dimacst::write_dimacs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cbmc_dimacst::write_dimacs(const std::string &filename)
{ 
  if(filename.empty() || filename=="-")
    return write_dimacs(std::cout);

  std::ofstream out(filename.c_str());

  if(!out)
  {
    error() << "failed to open " << filename << eom;
    return false;
  }

  return write_dimacs(out);
}

/*******************************************************************\

Function: cbmc_dimacst::write_dimacs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cbmc_dimacst::write_dimacs(std::ostream &out)
{
  dynamic_cast<dimacs_cnft&>(prop).write_dimacs_cnf(out);

  // we dump the mapping variable<->literals
  for(bv_cbmct::symbolst::const_iterator
      s_it=get_symbols().begin();
      s_it!=get_symbols().end();
      s_it++)
  {
    if(s_it->second.is_constant())
      out << "c " << (s_it->second.is_true()?"TRUE":"FALSE") << " "
          << s_it->first << "\n";
    else
      out << "c " << s_it->second.dimacs() << " "
          << s_it->first << "\n";
  }

  // dump mapping for selected bit-vectors
  const boolbv_mapt &boolbv_map=get_map();

  for(boolbv_mapt::mappingt::const_iterator
      m_it=boolbv_map.mapping.begin();
      m_it!=boolbv_map.mapping.end();
      m_it++)
  {
    if(m_it->second.bvtype==IS_SIGNED ||
       m_it->second.bvtype==IS_UNSIGNED)
    {
      const boolbv_mapt::literal_mapt &literal_map=m_it->second.literal_map;
      out << "c " << m_it->first;

      for(unsigned i=0; i<literal_map.size(); i++)
        if(!literal_map[i].is_set)
          out << " " << "?";
        else if(literal_map[i].l.is_constant())
          out << " " << (literal_map[i].l.is_true()?"TRUE":"FALSE");
        else
          out << " " << literal_map[i].l.dimacs();

      out << "\n";
    }
  }
  
  return false;
}
