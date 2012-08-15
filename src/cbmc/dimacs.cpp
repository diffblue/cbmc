/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <solvers/sat/dimacs_cnf.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

Function: bmct::write_dimacs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::write_dimacs()
{
  const std::string &filename=options.get_option("outfile");
  
  if(filename.empty() || filename=="-")
    return write_dimacs(std::cout);

  std::ofstream out(filename.c_str());
  if(!out)
  {
    std::cerr << "failed to open " << filename << std::endl;
    return false;
  }

  return write_dimacs(out);
}

/*******************************************************************\

Function: bmct::write_dimacs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::write_dimacs(std::ostream &out)
{
  dimacs_cnft dimacs_cnf;
  dimacs_cnf.set_message_handler(get_message_handler());

  bv_cbmct bv_cbmc(ns, dimacs_cnf);

  do_conversion(bv_cbmc);

  bv_cbmc.dec_solve();

  dimacs_cnf.write_dimacs_cnf(out);

  // we dump the mapping variable<->literals
  for(prop_convt::symbolst::const_iterator
      s_it=bv_cbmc.get_symbols().begin();
      s_it!=bv_cbmc.get_symbols().end();
      s_it++)
  {
    if(s_it->second.is_constant())
      out << "c " << (s_it->second.is_true()?"TRUE":"FALSE") << " "
          << s_it->first << std::endl;
    else
      out << "c " << s_it->second.dimacs() << " "
          << s_it->first << std::endl;
  }

  // dump mapping for selected bit-vectors
  const boolbv_mapt &boolbv_map=bv_cbmc.get_map();

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

      out << std::endl;
    }
  }
  
  return false;
}
