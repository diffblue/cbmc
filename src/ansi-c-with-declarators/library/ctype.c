
/* FUNCTION: isalnum */

inline int isalnum(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z') || (c>='0' && c<='9'); }

/* FUNCTION: isalpha */

inline int isalpha(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z'); }

/* FUNCTION: isblank */

inline int isblank(int c)
{ return c==' ' || c=='\t'; }

/* FUNCTION: iscntrl */

inline int iscntrl(int c)
{ return (c>=0 && c<='\037') || c=='\177'; }

/* FUNCTION: isdigit */

inline int isdigit(int c)
{ return c>='0' && c<='9'; }

/* FUNCTION: isgraph */

inline int isgraph(int c)
{ return c>='!' && c<='~'; }

/* FUNCTION: islower */

inline int islower(int c)
{ return c>='a' && c<='z'; }

/* FUNCTION: isprint */

inline int isprint(int c)
{ return c>=' ' && c<='~'; }

/* FUNCTION: ispunct */

inline int ispunct(int c)
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

inline int isspace(int c)
{ return c=='\t' ||
         c=='\n' ||
         c=='\v' ||
         c=='\f' ||
         c=='\r' ||
         c==' '; }

/* FUNCTION: isupper */

inline int isupper(int c)
{ return c>='A' && c<='Z'; }

/* FUNCTION: isxdigit */

inline int isxdigit(int c)
{ return (c>='A' && c<='F') || (c>='a' && c<='f') || (c>='0' && c<='9'); }

/* FUNCTION: tolower */

inline int tolower(int c)
{ return (c>='A' && c<='Z')?c+('a'-'A'):c; }

/* FUNCTION: toupper */

inline int toupper(int c)
{ return (c>='a' && c<='z')?c-('a'-'A'):c; }

