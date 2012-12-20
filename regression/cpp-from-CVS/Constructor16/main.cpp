class A
{
public:
  A(){};

private:
  A(const A&);               // disabled
  A& operator=(const A&);    // disabled
};

class B: public A
{
};


int main()
{
  B b1,b2;
  b1 = b2;  // not ok
}
