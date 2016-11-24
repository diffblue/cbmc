typedef decltype(nullptr) nullptr_t;

static_assert(nullptr==0, "nullptr==0");

#ifdef __GNUC__
static_assert(__nullptr==0, "__nullptr==0");
#endif

void something(int *p)
{
}

int main()
{
  nullptr_t my_null;
  my_null=nullptr;
  my_null=0;
  
  void *p=my_null;
  
  something(nullptr);
}


