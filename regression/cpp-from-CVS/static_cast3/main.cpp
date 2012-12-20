struct A {
	int i;
};

struct B {
	char j;
};

struct C: A, B
{
	bool k;
};


int main()
{
	C c;
	c.k = true;

	B& b = c;
	assert((static_cast<C&>(b)).k == true);

	B* pb = &c;
	static_cast<C*>(pb)->k = false;
	assert(c.k==false);
}
