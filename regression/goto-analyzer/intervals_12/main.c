
int main (void) {
  int i;
  int j;

  if (i <= 0 && j < i)
    __CPROVER_assert(j < 0, "j < 0");

  if (j < i && i <= 0)
    __CPROVER_assert(j < 0, "j < 0");

  return 0;
}


