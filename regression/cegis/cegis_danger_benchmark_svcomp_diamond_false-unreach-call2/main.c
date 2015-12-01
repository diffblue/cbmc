// Adapted version of diamond_true-unreach-call2 in SVCOMP.

int main(void) {
  unsigned int x=0;
  unsigned int y;

  while (x < 99) {
    if (y % 2 == 0) x++;
    else x += 2;

    if (y % 2 == 0) x += 2;
    else x -= 2;

    if (y % 2 == 0) x += 2;
    else x += 2;

    if (y % 2 == 0) x += 2;
    else x -= 2;

    if (y % 2 == 0) x += 2;
    else x += 2;

    if (y % 2 == 0) x += 2;
    else x -= 4;

    if (y % 2 == 0) x += 2;
    else x += 4;

    if (y % 2 == 0) x += 2;
    else x += 2;

    if (y % 2 == 0) x += 2;
    else x -= 4;

    if (y % 2 == 0) x += 2;
    else x -= 4;
  }

  __CPROVER_assert((x % 2) == (y % 2), "A");
  return 0;
}
