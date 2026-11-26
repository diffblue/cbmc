#include <string>

// constructing and assigning std::string from a `const char *' tries the
// constructors constrained by _If_sv, whose substitution fails silently; the
// error about the unknown function must not be prefixed by their
// instantiation contexts
int main()
{
  const char *p = "ab";
  std::string s;
  s = p;
  std::string t(p, 2);
  undeclared_function();
  return 0;
}
