class A
{
  int i;

public:
  A():i(1) { }
  ~A() { i=0; }
};

int main()
{
  A a;
}
