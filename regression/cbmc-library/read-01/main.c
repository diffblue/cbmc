#ifdef _WIN32
#include <io.h>
#else
#include <unistd.h>
#endif

#include <stdio.h>

int main()
{
	char data[20];

	if(read(0, data, 100) < 0)
		printf("An error has occurred");
	else
		printf("Read occurred");

	return 0;
}
