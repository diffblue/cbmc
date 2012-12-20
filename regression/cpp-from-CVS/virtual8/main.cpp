int g1;
int g2;

class A
{
	public:
	virtual ~A(){g1 = g2+1;}
};

class B: public A
{
	public:
	~B(){g2 = 1;}
};

int main()
{
	A* pA = new B();
	delete pA;
	assert(g2==1);
	assert(g1==2);
}
