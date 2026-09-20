// Tentative definition of an incomplete array (C standard 6.9.2, paragraph 5).
// The C front-end adjusts this to an array of size 1 during typecheck, i.e.
// before linking. This must still link cleanly against the extern declaration
// of the same array in another translation unit (ref.c).
int arr[];

int get(int i)
{
  return arr[i];
}
