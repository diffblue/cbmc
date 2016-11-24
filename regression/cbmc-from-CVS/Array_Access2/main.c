int a[4];
int *p;

int main() {
	int j;

	a[1] = 1;

	p = a;
	p++;
	a[0] = 1;
	*p = 1;

	j = a[0];
	assert(j == 1);

	j = a[1];
	assert(j == 1);
}
