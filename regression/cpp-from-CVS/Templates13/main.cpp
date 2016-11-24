template
<class T>
bool func(){
	return func<bool>();
}

template <>
bool func<bool>()
{
	return true;
}

int main()
{
	assert(func<int>());
}
