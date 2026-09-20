// Declaration referencing the array defined (tentatively) in def.c.
extern int arr[];
int get(int);

int main()
{
  // arr is adjusted to size 1 and zero-initialised; reading element 0 yields 0.
  __CPROVER_assert(get(0) == 0, "tentative array element is zero-initialised");
  return 0;
}
