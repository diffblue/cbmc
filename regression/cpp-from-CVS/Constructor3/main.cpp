class x
{
public:
  x();
  x(int z);
  int i;
};

x::x():i(1) { }
x::x(int z):i(z) { }

int main()
{
  x a(5);
  assert(a.i==5);
}

