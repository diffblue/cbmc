struct A {
	bool operator[](int index) {return true;}
};

struct B {
	A a;
	bool operator[](int index) {return false;}
	bool func(){return a[0];}
};

int main()
{
	B b;
	assert(b.func()==true);
}
