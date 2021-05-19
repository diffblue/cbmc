typedef void(keyhandler_fn_t)(void);
typedef void(irq_keyhandler_fn_t)(int);

void foo()
{
}

struct keyhandler
{
  union {
    keyhandler_fn_t *fn;
    irq_keyhandler_fn_t *irq_fn;
  };
  const char *desc;
  _Bool x, y;
} key_table[3] = {[0] = {{(keyhandler_fn_t *)(foo)}, "text", 1, 0}};

int main()
{
}
