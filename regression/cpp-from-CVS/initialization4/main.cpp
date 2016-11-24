int g;

int gen()
{
  return g++;
}

const int b = gen();
const int a = gen();

int main()
{
	assert(a==1);
	assert(b==0);
}
