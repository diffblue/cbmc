class A
{
	int i;
	A(int i):i(i){}
	private:
	A(); // disabled
};

class B: A
{
};

