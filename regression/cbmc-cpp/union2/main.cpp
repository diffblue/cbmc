struct A
{
  union
  {
    int a;
    char b;
  };
};

int main()
{
  A obj;
  obj.a = 'z';
  assert(obj.b=='z'); // little endian assumption
  assert(sizeof(A) == sizeof(int));
}
