struct B {
	int i;
	bool operator == (int b)
	{
		return i == b;
	}
};

struct A {
	int i;
	operator B() const
	{
		B b;
		b.i = i;
		return b;
	}
};

int main() {
	A a;
	a.i = 10;
	assert( a.operator B() == 10 );
}
