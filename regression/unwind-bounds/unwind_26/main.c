
int f00 (int x) {
	do {
		int y;
		y = x + x;
		x = y;
	} while (0);

	return x;
}

int main() {
  f00(0);
}

