#include <cstring>
extern "C" void __CPROVER_assert(bool, const char *);
struct pattern
{
  char *text;
  // a function used only in the bound of an array new-expression (from the
  // C library, which provides it only if it is referenced)
  void copy(const char *source)
  {
    text = new char[1 + ::strlen(source)];
    std::strcpy(text, source);
  }
};
int main()
{
  pattern p;
  p.copy("ab");
  __CPROVER_assert(p.text[1] == 'b' && p.text[2] == 0, "copied");
  delete[] p.text;
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
