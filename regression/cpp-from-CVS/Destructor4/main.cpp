class A
{
	public:
	int i;
	A():i(1){}
	~A();
};

A::~A()
{
	i = -1;
}

int main()
{
	A a;
}
