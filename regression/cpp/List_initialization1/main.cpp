int somewhat { 123 };

int some_function(int)
{
  return { 1 };
}

class some_class
{
  int member1 { 1 };
  int member2 = { 2 };
};

class other_class
{
  other_class():member { 1 }
  {
  }

  int member;
};

int main()
{
  int x, *p;
  int y { 1 };
  x={ 1 };
  x=int { 1 };
  x=(int) { 1 };
  p=new int { 1 };
  some_function({1});
}
