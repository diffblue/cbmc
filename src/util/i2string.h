/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

std::string i2string(int i);
std::string i2string(signed long int i);
std::string i2string(unsigned i);
std::string i2string(unsigned long int i);

// 64 bit integers

#ifdef _MSC_VER
std::string i2string(signed __int64 i);
std::string i2string(unsigned __int64 i);
#endif
