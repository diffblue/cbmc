struct hh{
  unsigned short h1;
  unsigned short h2;
};
union uuu {
  unsigned int l;
  struct hh h;
};

int main()
{
  union uuu ebx = {0};
  ebx.l=10;
  assert(ebx.l<1000);
}
