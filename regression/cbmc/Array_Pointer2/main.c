int nums[2];
int *p;

int main() {
	nums[1] = 999;
	p = &nums[0];
	p++;

	assert(*p == 999);
}
