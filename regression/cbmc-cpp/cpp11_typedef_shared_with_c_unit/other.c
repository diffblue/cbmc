#include "shared.h"

int common(int x, locale_handle l)
{
  (void)l;
  return x + 1;
}

// the inline definition of wrap in this unit, which C requires
extern int wrap(int, locale_handle);
