struct X
{
  int i;
};
// [class.mi]/3: a class shall not be a direct base more than once
struct Y : X, X
{
};
int main()
{
  Y y;
}
