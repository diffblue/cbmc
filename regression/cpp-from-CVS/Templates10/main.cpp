template <class T>
int func()
{
	return 0;
}

template <>
int func<int>()
{
	return 1;
}

template <>
int func<char>()
{
	return 2;
}

int main()
{
	assert(func<bool>() == 0);
	assert(func<int>()  == 1);
	assert(func<char>() == 2);
}
