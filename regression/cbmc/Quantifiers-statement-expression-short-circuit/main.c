#include <assert.h>

int main(void)
{
  // When the body of a quantifier is a statement expression with &&
  // short-circuiting, the path that skips the final expression must
  // contribute false.  Without this, the exists body "vacuously"
  // holds for all values outside the LHS range.

  // exists q. q < 4 && ({int r = q > 10; r;}) - impossible, must fail
  assert(__CPROVER_exists {
    unsigned long q;
    ({
      q < 4 && ({
        int r = q > 10;
        r;
      });
    })
  });

  // forall q. q < 4 && ({int r = q < 10; r;}) - fails for q >= 4
  assert(__CPROVER_forall {
    unsigned long q;
    ({
      q < 4 && ({
        int r = q < 10;
        r;
      });
    })
  });

  // Nested: exists q. q<4 && ({int r = q>2 && ({int s = q>10; s;}); r;})
  assert(__CPROVER_exists {
    unsigned long q;
    ({
      q < 4 && ({
        int r = q > 2 && ({
                  int s = q > 10;
                  s;
                });
        r;
      });
    })
  });

  return 0;
}
