class T
{
public:
};

int operator+(T a, int b)
{
  return b;
}

int operator-(T a, int b)
{
  return -b;
}

int main()
{
  T x;

  int temp;
  
  temp=x+2;
  assert(temp==2);
  
  temp=x-3;
  assert(temp==-3);
}
