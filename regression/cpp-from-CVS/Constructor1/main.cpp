class t1
{
public:
  int i;
  
  t1() { i=1; }
};

class t2
{
public:
  int i;
  
  t2():i(2) { }
};

class t3
{
public:
  int i;
  
  t3();
};

t3::t3():i(3)
{
}

int main()
{
  t1 instance1;
  assert(instance1.i==1);
  
  t2 instance2;
  assert(instance2.i==2);

  t2 *p=new t2;
  assert(p->i==2);
  delete p;

  t3 instance3;
  assert(instance3.i==3);
}
