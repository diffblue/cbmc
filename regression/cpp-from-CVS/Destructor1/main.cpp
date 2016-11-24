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

  {
    t1 instance1;
    assert(g==1);
  }
  
  assert(g==2);
}
