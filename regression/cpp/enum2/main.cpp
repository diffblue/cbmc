enum e1 { A } a;
enum e2 { B1, B2 } b;

static_assert(((e1)B1)==A, "casting between enums");

int main()
{
  b=B1;
  a=(e1)b; // needs explicit cast
}
