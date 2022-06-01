
/* FUNCTION: isalnum */

int isalnum(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z') || (c>='0' && c<='9'); }

/* FUNCTION: isalpha */

int isalpha(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z'); }

/* FUNCTION: isblank */

int isblank(int c)
{ return c==' ' || c=='\t'; }

/* FUNCTION: iscntrl */

int iscntrl(int c)
{ return (c>=0 && c<='\037') || c=='\177'; }

/* FUNCTION: isdigit */

int isdigit(int c)
{ return c>='0' && c<='9'; }

/* FUNCTION: isgraph */

int isgraph(int c)
{ return c>='!' && c<='~'; }

/* FUNCTION: islower */

int islower(int c)
{ return c>='a' && c<='z'; }

/* FUNCTION: isprint */

int isprint(int c)
{ return c>=' ' && c<='~'; }

/* FUNCTION: ispunct */

int ispunct(int c)
{ return c=='!' ||
         c=='"' ||
         c=='#' ||
         c=='$' ||
         c=='%' ||
         c=='&' ||
         c=='\'' ||
         c=='(' ||
         c==')' ||
         c=='*' ||
         c=='+' ||
         c==',' ||
         c=='-' ||
         c=='.' ||
         c=='/' ||
         c==':' ||
         c==';' ||
         c=='<' ||
         c=='=' ||
         c=='>' ||
         c=='?' ||
         c=='@' ||
         c=='[' ||
         c=='\\' ||
         c==']' ||
         c=='^' ||
         c=='_' ||
         c=='`' ||
         c=='{' ||
         c=='|' ||
         c=='}' ||
         c=='~'; }

/* FUNCTION: isspace */

int isspace(int c)
{ return c=='\t' ||
         c=='\n' ||
         c=='\v' ||
         c=='\f' ||
         c=='\r' ||
         c==' '; }

/* FUNCTION: isupper */

int isupper(int c)
{ return c>='A' && c<='Z'; }

/* FUNCTION: isxdigit */

int isxdigit(int c)
{ return (c>='A' && c<='F') || (c>='a' && c<='f') || (c>='0' && c<='9'); }

/* FUNCTION: tolower */

int tolower(int c)
{ return (c>='A' && c<='Z')?c+('a'-'A'):c; }

/* FUNCTION: toupper */

int toupper(int c)
{ return (c>='a' && c<='z')?c-('a'-'A'):c; }
