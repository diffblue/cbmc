// C++11 anonymous class with base specifier
struct Base
{
  int x;
};
struct : Base
{
  int y;
} obj;

int main()
{
  obj.x = 1;
  obj.y = 2;
  return 0;
}
