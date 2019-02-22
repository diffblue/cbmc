void checkpoint()
{
}

struct S
{
  int c1;
  int c2;
};

struct S st = {1, 2};

int main()
{
  st.c2 = 3;

  checkpoint();

  return 0;
}
