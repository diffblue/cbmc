int main(int argc, char *argv[])
{
  __CPROVER_assert(sizeof(unsigned int) == 2, "[--16] size of int is 16 bit");
  __CPROVER_assert(
    sizeof(unsigned long) == 4, "[--LP32] size of long is 32 bit");

  unsigned int k = non_det_unsigned();
  __CPROVER_assume(k < 1);
  __CPROVER_assert(k != 0xffff, "false counter example 16Bit?");

  return 0;
}
