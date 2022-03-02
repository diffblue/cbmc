int main()
{
#ifndef WIDE
  'abcde';
#else
  (void)L'abcde';
#endif
}
