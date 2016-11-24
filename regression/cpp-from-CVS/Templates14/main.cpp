
namespace n1
{
	template <class S>
	struct A{
		S a;
	};
}

template <class T>
struct B{
	n1::A<T> b;
};

int main()
{
	B<bool> o;
	o.b.a = true;
	assert(o.b.a==true);
};
