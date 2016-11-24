template <class T>
bool func(T t){return false;}


template <>
bool func<int>(int t){return true;}

template <class A>
struct Test
{
	bool f()
	{
		A a;
		return func<A>(a);
	}
};

int main()
{
	Test<int> t1;
	assert(t1.f()==true);
}
