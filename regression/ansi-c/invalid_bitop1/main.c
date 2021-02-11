int main()
{
  int *p;
  // bitand and shift are correctly rejected by the C front-end
  // p = p & 0;
  // p = p << sizeof(int *) * 8;
  p <<= sizeof(int *) * 8;
}
