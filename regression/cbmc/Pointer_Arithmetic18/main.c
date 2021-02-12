#define MB 0x00100000
#define BASE (15 * MB)
#define OFFSET (1 * MB)

main()
{
  char *base = BASE;
  int offset = OFFSET;
  int n = 2;
  __CPROVER_assert(&((char *)base)[offset] != 0, "no wrap-around expected");
}
