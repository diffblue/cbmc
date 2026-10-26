// N5008 [expr.delete]/2: in an array delete expression, the operand may be a
// pointer value that resulted from a previous array new-expression.  A
// malloc between the new-expression and the delete-expression does not
// change that.  libc++'s basic_filebuf allocates its buffers with new[] and
// opens the file with fopen (a malloc in CBMC's C library) before its
// destructor deletes them.
extern "C" void *malloc(__CPROVER_size_t);
extern "C" void free(void *);
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  char *array = new char[4];
  void *other = malloc(8);
  delete[] array;
  free(other);
  int reached = 1;
  __CPROVER_assert(reached == 1, "array deleted");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
  return 0;
}
