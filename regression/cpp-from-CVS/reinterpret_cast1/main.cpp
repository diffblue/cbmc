int main()
{
	int v = 256;
	int *i= &v;
	char *c = reinterpret_cast<char *>(i);
	*c == 0;
	int *j = reinterpret_cast<int *>(c);
	assert(j==i);
}
