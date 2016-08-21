template<class fitness_testert>
void prepare_fitness_tester_library(fitness_lib_handlet &handle,
    fitness_testert &fitness_tester,
    const std::function<std::string(void)> &source_code_provider,
    const std::string &library_file_path, const std::string compile_options)
{
  if (fitness_tester) return;
  void * const func=prepare_fitness_tester_library(handle, source_code_provider,
      library_file_path, compile_options);
  fitness_tester=reinterpret_cast<const fitness_testert &>(func);
}

template<class fitness_testert>
void close_fitness_tester_library(fitness_lib_handlet &handle,
    fitness_testert &fitness_tester)
{
  close_fitness_tester_library(handle);
  if (fitness_tester) fitness_tester=0;
}
