void __CPROVER_assert();
template <long, class...> void get(int);
template <int, class> void get(void) {}
int main_t;
int main() { get<0>(main_t); }
