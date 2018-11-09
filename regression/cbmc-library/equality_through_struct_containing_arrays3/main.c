#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t literal;

literal neg(literal l)
{
  return l ^ 0x1;
}

typedef struct _clause
{
  struct clause *wl_next;
  struct clause *wl_prev;

  literal first_watch;
  literal second_watch;

  // End of first 16-byte cache line (on 32 bit machines)

  uint32_t length;
  literal body[0];

} clause;

clause *createClause(literal *lits, uint32_t count)
{
  assert(count >= 2);

  size_t s = sizeof(clause) + count * sizeof(literal);
  clause *c = malloc(s);

  memset(c, 0, s);

  c->length = c;
  c->first_watch = lits[0];
  c->second_watch = lits[1];

  for(uint32_t i = 2; i < count; ++i)
  {
    c->body[i - 2] = lits[i];
  }

  return c;
}

int main(void)
{
  uint32_t line[4] = {0x23, 0x42, 0x43, 0x22};

  clause *c = createClause(line, 4);

  assert(c->wl_next == NULL);
  assert(c->wl_prev == NULL);
  assert(neg(c->body[1]) == 0x23);

  return 1;
}
