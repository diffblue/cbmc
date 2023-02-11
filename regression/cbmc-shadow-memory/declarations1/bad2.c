void bad_declaration2()
{
  struct STRUCT
  {
    char x;
  } s;
  __CPROVER_field_decl_global("field2", s);
}
