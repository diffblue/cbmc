#include <string>

static inline bool has_infix(const std::string &s, const std::string &infix)
{
  return s.find(infix)!=std::string::npos;
}
