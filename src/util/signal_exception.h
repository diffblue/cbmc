#include <util/i2string.h>

class signal_exceptiont: public std::exception
{
 public:
  signal_exceptiont(int _s) {
    s = _s;
  } 
  
  virtual const char* what() const throw() {
    return (std::string("caught signal ")+i2string(s)).c_str();
  }

 protected:
  int s;
};
