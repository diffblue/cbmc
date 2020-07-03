void main(int argc, char *argv[])
{
  float x = 2.5;
  float y = 1.5;
  int z = 0;

  if(x > y)
    z = 1;

  __CPROVER_assert(z == 1, "x > y, z == 1");

  y = 2.6;

  if(x > y)
    z = 3;

  __CPROVER_assert(z == 1, "x < y, z == 1");
}
