class B
{
public:
	virtual int f() const {return 0;}
};

class A: public B
{
public:
	int f() {return 1;}
};

int main()
{
	A a;
	B b = (B) a;
	assert(b.f()==0);
	assert(a.f()==1);
}
