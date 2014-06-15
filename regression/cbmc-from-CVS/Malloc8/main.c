#include <stdio.h>
#include <stdlib.h>

struct person {
	char* name;
};

int main() {
	struct person** ptr_ptr_p1;
	ptr_ptr_p1 = malloc(sizeof(struct person*));
        *ptr_ptr_p1 = malloc(sizeof(struct person));
	
	// Piecewise assignments are ok with cbmc
	struct person* ptr_p;
	ptr_p = *ptr_ptr_p1; 
	ptr_p->name = "Dummy";
	printf("%s\n", ptr_p->name);

	// Too many dereferences cause trouble, uncomment next statement to get error message
 	(*ptr_ptr_p1)->name = "Dummy";
	printf("%s\n", (*ptr_ptr_p1)->name);

	// This code block causes a SYMEX Error message, uncomment to see it
	struct person** ptr_ptr_p2;
        (*ptr_ptr_p2)->name = "Hallo";
        printf("%s\n", (*ptr_ptr_p2)->name);

	return 0;
}
