struct A
{
	bool True(){return true;}
};

struct B
{
	A a;
	A* operator->(){return &a;}
};

struct C
{
	B b;
	B& operator->(){return b;}
};

int main()
{
	C c;
	assert(c->True());
}
