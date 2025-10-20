union U
{
  unsigned char buf[2];
} s;

int main()
{
  __CPROVER_assert(s.buf[0] == 0, "");
}
