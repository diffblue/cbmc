bool f(char c)
{
	return false;
}

bool f(int i, int j = 0)
{
	return true;
}

int main()
{
	assert(f(5));
	return 0;
}
