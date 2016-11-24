struct B
{
	int i;
};


struct A {
	B b;
	A(int i){b.i = i;}
	operator B& ()
	{
		return b;
	}
};

int get_i(const B& b){return b.i;}

int main()
{
	A a(10);
	assert(get_i(a)==10);
}
