
short  ret_const()
{
  return 123;
}


unsigned long save_res0, save_res1;


int f0()
{
  short res = 0;

  res += ret_const();  // <-- fails
  //res = ret_const();   // <-- OK
  //res += 123;          // <-- OK

  save_res0 = res;

  return 0;
}


int f1()
{
  short res = 0;

  res += ret_const();  // <-- fails
  //res = ret_const();   // <-- OK
  //res += 123;          // <-- OK

  save_res1 = res;

  return 0;
}


int main()
{
  f0();
  f1();

  assert( save_res0 == save_res1 );
}
