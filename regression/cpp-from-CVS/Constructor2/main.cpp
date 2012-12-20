class t1
{
public:
  int i;
  
  t1();
  t1(int z);
};

t1::t1():i(1)
{
}

t1::t1(int z)
{
  i=z;
}

class t2
{
public:
  int i;
  
  t2();
  t2(int z);
};

t2::t2():i(1)
{
}

t2::t2(int z)
{
}

int main()
{
  t1 instance1(5);
  assert(instance1.i==5);  
}
