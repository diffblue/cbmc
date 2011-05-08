/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CVC_DEC_H
#define CPROVER_PROP_CVC_DEC_H

#include <fstream>

#include "cvc_conv.h"

class cvc_temp_filet
{
public:
  cvc_temp_filet();
  ~cvc_temp_filet();

protected:  
  std::ofstream temp_out;
  std::string temp_out_filename, temp_result_filename;
};

class cvc_dect:protected cvc_temp_filet, public cvc_convt
{
public:
  explicit cvc_dect(const namespacet &_ns):cvc_convt(_ns, temp_out)
  {
  }
  
  virtual resultt dec_solve();
  
protected:
  resultt read_cvcl_result();
  void read_assert(std::istream &in, std::string &line);
};

#endif
