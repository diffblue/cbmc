class  A
{
  public:
  int&  i;
  A(int &i):i(i){}
  private:
  A& operator=(const A&);
};

int main()
{
	int var;
	int& ref =var;
	var = 10;
	A a(var);
	a.i = 20;
	assert(var==20);
}
