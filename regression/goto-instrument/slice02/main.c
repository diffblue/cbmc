#include <stdio.h>

#define TRUE	(1)
#define FALSE	(0) 
#define SIZE	(10)
int topo=0;

void inc_topo(void){
	topo++;
}

void dec_topo(void){
	topo--;
}

int get_topo(void){
	return topo;
}

int stack_empty(void){
	(topo==0) ? TRUE : FALSE; 
}

int push(int *stack, int x){
	if (topo==SIZE) {
		printf("stack overflow\n");
		return -1;
	} else {
		stack[get_topo()] = x;
		printf("push: stack[%d] = %d\n", get_topo(), stack[get_topo()]);
		inc_topo();
	}
}

int pop(int *stack){
	if (get_topo()==0) {
		printf("stack underflow\n");	
		return -1;
	} else {
		dec_topo();
		printf("pop: stack[%d] = %d\n", get_topo(), stack[get_topo()]);
		return stack[get_topo()];  
	}
}

int main(void) {
	int arr[SIZE];

	push(arr,3);
	push(arr,4);
	push(arr,5);
	push(arr,1);
	push(arr,9);
	push(arr,10);
	push(arr,6);
	push(arr,12);
	push(arr,15);
	push(arr,8);
	push(arr,20);

	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);
	pop(arr);

}
