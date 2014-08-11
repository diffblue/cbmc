#define NULL ((void *)0)
typedef struct tag {
	int field;
} StructTag;

StructTag *TagTbl[2];

int main() {
	if(TagTbl[0] != NULL)
		TagTbl[0]->field = 1;
}
