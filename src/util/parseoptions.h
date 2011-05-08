/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DBOX_PARSEOPTIONS_H

#define DBOX_PARSEOPTIONS_H

#include <string>
#include "cmdline.h"

class parseoptions_baset
{
public:
  parseoptions_baset(
    const std::string &optstring, int argc, const char **argv);

  cmdlinet cmdline;
  
  virtual void help();
  virtual void usage_error();
  
  virtual int doit()=0;
  
  virtual int main();
  virtual ~parseoptions_baset() { }
  
private:
  bool parse_result;
};

#endif
