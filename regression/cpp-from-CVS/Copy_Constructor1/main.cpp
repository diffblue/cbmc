class A
{
	public:
	A():i(0){}
	virtual int  inc(){return ++i;}
	int i;
};

class B: public A
{
	public:
	int inc(){return i+=2;}
};

int main()
{
	B b;
	int c = b.inc();
	assert(c==2);
	A a=b;
	c = a.inc();
	assert(c==3);
}
