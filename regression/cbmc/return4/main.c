short f0(short x)
{
  int z;

  do {
    z=0;
    if(x <= 0) { z=1;
      return 100; }
  }
  while( x-- ); /* <-- The diff */

  z=2;
  return 200;
}

short f1(short x)
{
  do {
    if(x <= 0)
      return 100;
  }
  while( --x ); /* <-- The diff */

  return 200;
}


short f0_if(short x)
{
  if( x-- )
    return 200;

  if(x <= 0)
    return 100;

  return 0;
}

short f1_if(short x)
{
  if( --x )
    return 200;

  if(x <= 0)
    return 100;

  return 0;
}


short f0_wh(short x)
{
  while( x-- )  /* <-- The diff */
    if(x <= 0)
      return 100;

  return 200;
}

short f1_wh(short x)
{
  while( --x )  /* <-- The diff */
    if(x <= 0)
      return 100;

  return 200;
}


int main()
{
  int flag;
  short a;
  short res0, res1;

  if( flag )
    a = 1;
  else
    a = 1;

  res0 = f0(a);
  res1 = f1(a);

  assert(res0==100);
  assert(res1==200);

  res0 = f0(a);
  res1 = f1(a);

  assert(res0==100);
  assert(res1==200);

  res0 = f0_if(a);
  res1 = f1_if(a);

  assert(res0==200);
  assert(res1==100);

  res0 = f0_wh(a);
  res1 = f1_wh(a);

  assert(res0==100);
  assert(res1==200);

  return 0;
}
