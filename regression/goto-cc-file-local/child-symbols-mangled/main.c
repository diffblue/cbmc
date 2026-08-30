// A third TU including the same header, providing an entry point so the
// assertion-check variant can run cbmc on the linked model.  This verifies the
// linked model is usable -- i.e. the mangled child symbols and the symbol_expr
// references inside instruction bodies are consistent, not just the
// symbol-table keys.
#include "lib.h"

#include <assert.h>
int main(void)
{
  assert(helper(41) == 42);
  return 0;
}
