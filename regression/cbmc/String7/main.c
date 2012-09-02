struct S { 
  char *Operator;
};

const struct S b1006_props = { 
  .Operator = "OR"
};

void foo(struct S x) {
  char * s = x.Operator;
  assert(s[0]=='O');
}

void bar(struct S *x) {
  char * s = x->Operator;
  assert(s[0]=='O');
}

int main()
{
  assert(b1006_props.Operator[0]=='O');
  foo(b1006_props);
  bar(&b1006_props);
}
