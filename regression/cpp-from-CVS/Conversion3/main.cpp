int main()
{
	char c = 'c';
	int& i = c;	// ill-formed
	i++;
}
