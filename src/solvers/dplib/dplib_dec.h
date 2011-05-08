/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_DPLIB_DEC_H
#define CPROVER_PROP_DPLIB_DEC_H

#include <fstream>

#include "dplib_conv.h"

class dplib_temp_filet
{
public:
  dplib_temp_filet();
  ~dplib_temp_filet();

protected:  
  std::ofstream temp_out;
  std::string temp_out_filename, temp_result_filename;
};

class dplib_dect:protected dplib_temp_filet, public dplib_convt
{
public:
  explicit dplib_dect(const namespacet &_ns):
    dplib_convt(_ns, temp_out)
  {
  }
  
  virtual resultt dec_solve();
  
protected:
  resultt read_dplib_result();
  void read_assert(std::istream &in, std::string &line);
};

#endif
