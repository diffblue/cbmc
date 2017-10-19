int main()
{
  int i=0;
  __CPROVER_havoc_object(&i);
  __CPROVER_assert(i==0, "i==0"); // should fail

  int array[10];
  for(i=0; i<10; i++) array[i]=i;

  __CPROVER_havoc_object(array);
  __CPROVER_assert(array[3]==3, "array[3]"); // should fail

  struct { int i, j; } some_struct = { 1, 2 };
  __CPROVER_havoc_object(&some_struct.j);
  __CPROVER_assert(some_struct.i==1, "struct i"); // should fail
  __CPROVER_assert(some_struct.j==2, "struct j"); // should fail

  // now conditional
  _Bool c;
  int *p=c?&i:&some_struct.i;
  i=20;
  some_struct.i=30;
  __CPROVER_havoc_object(p);
  if(c)
  {
    __CPROVER_assert(i==20, "i==20 (A)"); // should fail
    __CPROVER_assert(some_struct.i==30, "some_struct.i==30 (A)"); // should pass
  }
  else
  {
    __CPROVER_assert(i==20, "i==20 (B)"); // should pass
    __CPROVER_assert(some_struct.i==30, "some_struct.i==30 (B)"); // should fail
  }
}
