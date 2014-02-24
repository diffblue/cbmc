/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

// One day, the below will be replaced by C++11's std::to_string.

std::string i2string(int i);
std::string i2string(signed long int i);
std::string i2string(signed long long int i);
std::string i2string(unsigned int i);
std::string i2string(unsigned long int i);
std::string i2string(unsigned long long int i);

