typedef void (*callback_t)(void);

struct xfer
{
  union { /*< FIX: union -> struct */
    struct
    {
      int *buf;
      callback_t callback; /*< FIX: remove */
    } a;
  };
} g_xfer;

int g_buf;

int main()
{
  g_xfer = (struct xfer){{{&g_buf}}};

  /* FIX, uncomment (only on cbmc develop 9ee5b9d6): */
  // g_xfer.a.buf = &g_buf;

  /* check the pointer was initialized properly */
  assert(g_xfer.a.buf == &g_buf);

  g_xfer.a.buf[0] = 42;          /* write a value via the pointer */
  assert(g_xfer.a.buf[0] == 42); /* check it was written */
  assert(g_buf == 42); /* the underlying value should also be updated */
}
