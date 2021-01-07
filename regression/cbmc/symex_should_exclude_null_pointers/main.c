#include <assert.h>

static void noop() { }

int main(int argc, char **argv) {

  int x;
  int *maybe_null = argc & 1 ? &x : 0;

  // There are two features of symex that might exclude null pointers: local
  // safe pointer analysis (LSPA for the rest of this file) and value-set
  // filtering (i.e. goto_symext::try_filter_value_sets()).

  // Should be judged safe by LSPA and value-set filtering (guarded by assume):
  int *ptr1 = maybe_null;
  __CPROVER_assume(ptr1 != 0);
  int deref1 = *ptr1;

  // Should be judged safe by LSPA and value-set filtering (guarded by else):
  int *ptr2 = maybe_null;
  if(ptr2 == 0)
  {
  }
  else
  {
    int deref2 = *ptr2;
  }

  // Should be judged safe by LSPA and value-set filtering (guarded by if):
  int *ptr3 = maybe_null;
  if(ptr3 != 0)
  {
    int deref3 = *ptr3;
  }

  // Should be judged unsafe by LSPA and safe by value-set filtering
  // (guarded by backward goto):
  int *ptr4 = maybe_null;
  goto check;

deref:;
  int deref4 = *ptr4;
  goto end_test4;

check:
  __CPROVER_assume(ptr4 != 0);
  goto deref;

end_test4:;

  // Should be judged unsafe by LSPA and safe by value-set filtering
  // (guarded by confluence):
  int *ptr5 = maybe_null;
  if(argc == 5)
    __CPROVER_assume(ptr5 != 0);
  else
    __CPROVER_assume(ptr5 != 0);
  int deref5 = *ptr5;

  // Should be judged unsafe by LSPA (due to suspicion write to ptr5 might alter
  // ptr6) and safe by value-set filtering:
  int *ptr6 = maybe_null;
  __CPROVER_assume(ptr6 != 0);
  ptr5 = 0;
  int deref6 = *ptr6;

  // Should be judged unsafe by LSPA (due to suspicion noop() call might alter
  // ptr7) and safe by value-set filtering:
  int *ptr7 = maybe_null;
  __CPROVER_assume(ptr7 != 0);
  noop();
  int deref7 = *ptr7;

  // Should be judged safe by LSPA and unsafe by value-set filtering (it
  // isn't known what symbol *ptr_ptr8 refers to, so null can't be removed
  // from a specific value set):
  int r8_a = 1, r8_b = 2;
  int *q8_a = argc & 2 ? &r8_a : 0;
  int *q8_b = argc & 4 ? &r8_b : 0;
  int **ptr8 = argc & 8 ? &q8_a : &q8_b;
  __CPROVER_assume(*ptr8 != 0);
  int deref8 = **ptr8;

  // Should be judged safe by LSPA and unsafe by value-set filtering (it
  // isn't known what symbol *ptr_ptr9 refers to, so null can't be removed
  // from a specific value set):
  int r9_a = 1, r9_b = 2;
  int *q9_a = argc & 2 ? &r9_a : 0;
  int *q9_b = argc & 4 ? &r9_b : 0;
  int **ptr9 = argc & 8 ? &q9_a : &q9_b;
  if(*ptr9 != 0)
    int deref9 = **ptr9;

  // Should be judged unsafe by LSPA and value-set filtering
  // (unsafe as only guarded on one branch):
  int *ptr10 = maybe_null;
  if(argc == 10)
    __CPROVER_assume(ptr10 != 0);
  else
  {
  }
  int deref10 = *ptr10;

  assert(0);
}
