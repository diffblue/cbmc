struct A
{
	protected:
	int i;
  int get_i(){return i;}

	A(int i):i(i){};
	
};

struct B: A
{
	B():A(0){}
};

B b;

int main()
{
	assert(b.get_i()==0);
}
