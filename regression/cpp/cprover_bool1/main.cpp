#include <limits.h>

static_assert(
  sizeof(bool[CHAR_BIT]) >= CHAR_BIT,
  "a bool is at least one byte wide");
static_assert(
  sizeof(__CPROVER_bool[CHAR_BIT]) == 1,
  "__CPROVER_bool is just a single bit");

int main(int argc, char *argv[])
{
}
