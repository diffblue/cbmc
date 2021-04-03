int main(int argc, char **argv)
{
  __CPROVER_assert(4 != argc, "assertion 4 != argc");
  argc++;
  argc--;
  __CPROVER_assert(argc >= 0, "assertion argc >= 0");
  __CPROVER_assert(argc != 4, "assertion argc != 4");
  argc++;
  argc--;
  __CPROVER_assert(argc + 1 != 5, "assertion argc + 1 != 5");
  return 0;
}
