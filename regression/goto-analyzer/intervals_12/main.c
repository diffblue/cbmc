
int main (void) {
  int i;
  int j;

  if (i <= 0 && j < i)
    assert(j < 0);

  if (j < i && i <= 0)
    assert(j < 0);

  return 0;
}


