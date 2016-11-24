struct A
{
	virtual bool func() const {return true;}
	virtual bool func()  {return false;}
};

int main()
{
	const A a1;
	assert(a1.func()== true);
	A a2;
	assert(a2.func()== false);
}
