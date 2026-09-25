// A constant static initializer that nests a compound literal projected
// through a union member -- the shape of the kernel's dynamic-debug
// _ddebug descriptor whose .key union is initialised from the
// STATIC_KEY_FALSE_INIT compound literal.  Before member-of-compound-
// literal simplification, the typechecker rejected this with "expected
// constant expression".
typedef struct
{
  int counter;
} atomic_t;

struct static_key
{
  atomic_t enabled;
  union
  {
    unsigned long type;
    void *entries;
  };
};

struct static_key_false
{
  struct static_key key;
};
struct static_key_true
{
  struct static_key key;
};

#define STATIC_KEY_INIT_FALSE                                                  \
  {                                                                            \
    .enabled = {0},                                                            \
    {                                                                          \
      .type = 0ul                                                              \
    }                                                                          \
  }
#define STATIC_KEY_FALSE_INIT                                                  \
  (struct static_key_false)                                                    \
  {                                                                            \
    .key = STATIC_KEY_INIT_FALSE,                                              \
  }

struct ddebug
{
  const char *function;
  unsigned flags;
  union
  {
    struct static_key_true dd_key_true;
    struct static_key_false dd_key_false;
  } key;
};

int main(void)
{
  static struct ddebug d = {
    .function = __func__,
    .flags = 0,
    .key.dd_key_false = (STATIC_KEY_FALSE_INIT),
  };
  __CPROVER_assert(
    d.key.dd_key_false.key.enabled.counter == 0,
    "compound-literal member folds to its constant");
  return 0;
}
