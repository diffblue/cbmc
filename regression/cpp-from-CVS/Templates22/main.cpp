template<class T>
T func(T* t){return *t;}

template<class T>
T func(T t){ return t;}

int main()
{
	int x = 10;
	assert(func<int>(&x) == func<int>(x));
}
