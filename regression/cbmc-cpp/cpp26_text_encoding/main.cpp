// N5008 [text.encoding]: UTF-8.
#include <text_encoding>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::text_encoding e{"UTF-8"};
  __CPROVER_assert(e.mib() == std::text_encoding::id::UTF8, "UTF-8");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
