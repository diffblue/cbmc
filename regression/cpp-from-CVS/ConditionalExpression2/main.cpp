char a[1];
char b[2];

int main()
{
	char* c = true ? a : b;
	assert(*c == a[0]);
	return 0;
}


