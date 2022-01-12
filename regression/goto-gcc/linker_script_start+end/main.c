extern char src_start[];
extern char src_end[];
extern char dst_start[];

void *memcpy(void *dest, void *src, unsigned n)
{
  return (void *)0;
}

int main()
{
  memcpy(dst_start, src_start, (unsigned)src_end - (unsigned)src_start);
  return 0;
}
