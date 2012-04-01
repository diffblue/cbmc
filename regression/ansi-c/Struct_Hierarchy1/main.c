struct tag1 {
	struct tag2 {
		int f;
	} y;
} x;

int main() {
	x.y.f = 0;
}
