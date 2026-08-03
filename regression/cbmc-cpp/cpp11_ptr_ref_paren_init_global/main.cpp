// A namespace-scope reference-to-pointer with a PARENTHESIZED
// initializer (`void *&child(__left_);`, direct-initialization per
// N5008 [dcl.init.general]/16.2) is rejected with "invalid implicit
// conversion from 'void *' to 'void'" -- the declarator's pointer
// level is lost when the paren initializer is parsed (any T*&
// fails; plain T& works; the `= init` spelling works).  Distilled
// from the cvise reduction of cpp11_set_insert_libcxx, whose
// __tree::__insert_unique writes the new node through exactly such a
// reference (`__node_base_pointer& __child`).  g++/clang++ accept and
// verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

void *__left_;
void *&child(__left_);
int g = 42;

int main()
{
  child = &g;
  __CPROVER_assert(*static_cast<int *>(__left_) == 42, "through global ref");
}
