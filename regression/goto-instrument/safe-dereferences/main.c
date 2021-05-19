static void noop() { }

int main(int argc, char **argv) {

  int x;

  // Should work (guarded by assume):
  int *ptr1 = &x;
  __CPROVER_assume(ptr1 != 0);
  int deref1 = *ptr1;

  // Should work (guarded by else):
  int *ptr2 = &x;
  if(ptr2 == 0)
  {
  }
  else
  {
    int deref2 = *ptr2;
  }

  // Should work (guarded by if):
  int *ptr3 = &x;
  if(ptr3 != 0)
  {
    int deref3 = *ptr3;
  }

  // Shouldn't work yet despite being safe (guarded by backward goto):
  int *ptr4 = &x;
  goto check;

deref:;
  int deref4 = *ptr4;
  goto end_test4;

check:
  __CPROVER_assume(ptr4 != 0);
  goto deref;

end_test4:;

  // Shouldn't work yet despite being safe (guarded by confluence):
  int *ptr5 = &x;
  if(argc == 5)
    __CPROVER_assume(ptr5 != 0);
  else
    __CPROVER_assume(ptr5 != 0);
  int deref5 = *ptr5;

  // Shouldn't work (unsafe as only guarded on one branch):
  int *ptr6 = &x;
  if(argc == 6)
    __CPROVER_assume(ptr6 != 0);
  else
  {
  }
  int deref6 = *ptr6;

  // Shouldn't work due to suspicion *ptr6 might alter ptr7:
  int *ptr7 = &x;
  __CPROVER_assume(ptr7 != 0);
  ptr6 = 0;
  int deref7 = *ptr7;

  // Shouldn't work due to suspicion noop() call might alter ptr8:
  int *ptr8 = &x;
  __CPROVER_assume(ptr8 != 0);
  noop();
  int deref8 = *ptr8;
}
