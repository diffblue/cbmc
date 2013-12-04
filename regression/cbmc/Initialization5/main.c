extern int __VERIFIER_nondet_int(void);

typedef enum {
  LIST_BEG,
  LIST_END
} end_point_t;

typedef enum {
  ITEM_PREV,
  ITEM_NEXT
} direction_t;

void remove_one(end_point_t from)
{
  const direction_t next_field = (LIST_BEG == from) ? ITEM_NEXT : ITEM_PREV;
}

end_point_t rand_end_point(void)
{
  _Bool choice;
  if (choice)
    return LIST_BEG;
  else
    return LIST_END;
}

int main()
{
  remove_one(rand_end_point());

  __CPROVER_assert(0, "");

  return 0;
}
