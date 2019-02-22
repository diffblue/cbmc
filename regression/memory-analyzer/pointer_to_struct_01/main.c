void checkpoint()
{
}

struct S
{
  struct S *next;
};

struct S st;
struct S *p;

int main()
{
  st.next = &st;
  p = &st;

  checkpoint();

  return 0;
}
