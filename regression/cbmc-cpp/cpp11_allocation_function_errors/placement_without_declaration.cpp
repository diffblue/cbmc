struct P
{
  int x;
};
int main()
{
  alignas(P) unsigned char buffer[sizeof(P)];
  // operator new(std::size_t, void *) is declared by <new> only
  P *p = new(buffer) P;
  (void)p;
  return 0;
}
