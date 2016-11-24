class x
{
private:
  int i;
  
public:
  x();

  int get_i() { return i; }
};

x::x():i(1)
{
}

int main()
{
  x a;
  assert(a.get_i()==1);
}
