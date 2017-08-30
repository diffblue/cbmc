typedef struct
{
	char bogus;
} bb_mbstate_t;

int bb_wcrtomb(char *s, char wc, bb_mbstate_t *ps);

int bb_wcrtomb(char *s, char wc, bb_mbstate_t *ps)
{
	return 1;
}

int main() {
	bb_wcrtomb("foo", 'Z', (void*)1);
	return 0;
}
