struct A
{
	virtual int& func(int& i){return i;}
};

int main()
{
	A a;
	int i = 0;
	int j = 1;

	a.func(i) = j;
	assert(i==j);
}
