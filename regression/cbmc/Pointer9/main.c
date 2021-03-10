int nondet_int();

typedef struct str1 {
  int x;
} Str1;

Str1 st1;

#define NULL ((void*)0)


void f1(int *px)
{
  *px = 1234;
}

main()
{
  int flag;
  int *ref = NULL;
  int x = 0;
  st1.x = 0;

  __CPROVER_assume( flag == 1 );

  if( flag )
    ref = &st1.x;
  else
    ref = &x;

  f1(ref);

  //f1(&st1.x);  /* uncomment this - and everithing works OK. */

  assert( st1.x == 1234 );  /* <-- fails, this is the problem. */
  //assert( ref == &st1.x );  /* this one is OK. */
  //assert( st1.x == 0 );     /* this one fails - OK. */
  //assert( x == 12345 );     /* fails - OK */
}
