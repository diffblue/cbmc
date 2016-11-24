class X
{
public:
  ~X()
  {
  }
};

int main()
{
  const X *p=new X;

  // this is to work even though p is const, and the destructor
  // isn't.  
  delete p;
}
