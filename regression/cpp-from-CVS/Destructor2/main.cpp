int g;

class t1
{
public:
  t1() { g=1; }
  ~t1() { g=2; }
};

int main()
{
  assert(g==0);

  while(true)
  {
    {
      t1 instance1;
      assert(g==1);
      break; // leave the loop
    }

  }
  
  assert(g==2);
}
