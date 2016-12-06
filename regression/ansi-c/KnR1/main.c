struct stmt
{
  int x;
};

#ifdef __GNUC__
static void
deadstmt(s, last)
   register struct stmt * __attribute__((aligned)) s;
{
}
#endif

static void
deadstmt_const(s, last)
   register const struct stmt *s;
{
}

static void
deadstmt_const_nr(s, last)
   const struct stmt *s;
{
}

int (*d(a))()
  unsigned a;
{
  struct stmt s;
  deadstmt(&s, 0);
  deadstmt_const(&s, 0);
  deadstmt_const_nr(&s, 0);
  return 0;
}

int main()
{
  return d(-1)!=0;
}
