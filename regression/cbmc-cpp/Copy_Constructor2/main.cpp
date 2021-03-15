class A
{
public:
  A():i(0) { }
  virtual int inc() { return ++i; }
  int i;
};

class B: public A
{
public:
  int inc() { return i+=2; }
};

int inc(A a)
{
  return a.inc();
}

int main()
{
  B b;

  int c = b.inc();
  assert(c==2);

  c = inc((A)b);
  assert(c==3);
}
