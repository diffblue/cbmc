// C++11
// decltype is a C++11 feature to get the "declared type" of an expression.
// It is similar to 'typeof' but handles reference types "properly".

int x;
int y;
decltype(x + y) z;

int main()
{
  int &my_ref1=x;
  decltype(my_ref1) my_ref2=y;
}
