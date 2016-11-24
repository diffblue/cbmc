unsigned short array[4];

int main(void)
{
  unsigned short *buf;

  buf=array;

  // this isn't really ANSI-C
  *(((unsigned long *)buf)++);

  return 0;
}
