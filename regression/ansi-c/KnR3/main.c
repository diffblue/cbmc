// Debian package ircii
typedef unsigned char __u_char;
typedef __u_char u_char;

typedef struct WhoisStuffStru
{
 u_char *nick;
 u_char *user;
 u_char *host;
 u_char *channel;
 u_char *channels;
 u_char *name;
 u_char *server;
 u_char *server_stuff;
 u_char *away;
 int oper;
 int chop;
 int not_on;
} WhoisStuff;

static void (*
whois_func_head (server_index))(WhoisStuff *, u_char *, u_char *)
 int server_index;
{
 return ((void *)0);
}

int main()
{
  return whois_func_head(0)==0;
}
