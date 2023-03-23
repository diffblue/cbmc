void good_declarations()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);
  __CPROVER_field_decl_global("field2", (unsigned __CPROVER_bitvector[6])0);
}
