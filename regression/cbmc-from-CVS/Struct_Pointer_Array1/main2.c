#define NULL ((void *)0)
typedef struct tag {
	int field;
} StructTag;

StructTag *TagTbl[2];

int main() {
  unsigned int i;
  assume(i<2);
  
	if(TagTbl[i] != NULL)
		TagTbl[i]->field = 1;
}
