template<class counterexamplet_itert>
void print_jsa_counterexample(
    messaget::mstreamt &os,
    counterexamplet_itert first,
    const counterexamplet_itert last)
{
  for (; first != last; ++first) print_jsa_counterexample(os, *first);
}
