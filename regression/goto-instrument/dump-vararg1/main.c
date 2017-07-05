#include<stdarg.h>
#include<stdlib.h>

void bb_verror_msg(const char *s, va_list p, const char *strerr) {
}

void bb_error_msg(const char *s, ...)
{
    va_list p;
    va_start(p, s);
    bb_verror_msg(s, p, NULL);
    va_end(p);
}

int main() {
    bb_error_msg("FOOO");
    return 0;
}

