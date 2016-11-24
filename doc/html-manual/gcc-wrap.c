const char gcc[]="gcc";

#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include <sys/wait.h>
#include <sys/types.h>

void run(const char *what, char *const argv[])
{
  pid_t childpid; /* variable to store the child's pid */
  int retval;     /* child process: user-provided return code */

  /* now create new process */
  childpid = fork();
    
  if(childpid>=0) /* fork succeeded */
  {
    if(childpid==0) /* fork() returns 0 to the child process */
    {
      execvp(what, argv);
      /* usually no return */
      fprintf(stderr, "execp %s failed\n", what);
      exit(1);
    }
    else /* fork() returns new pid to the parent process */
    {
      int status;     /* parent process: child's exit status */
      wait(&status); /* wait for child to exit, and store its status */
      int code=WEXITSTATUS(status);
      if(code!=0) exit(code);
    }
  }
  else /* fork returns -1 on failure */
  {
    perror("fork failed"); /* display error message */
    exit(1);
  }
}
 
int main(int argc, char * argv[])
{
  // First do original call.
  
  // on some systems, gcc gets confused if it is not argument 0
  // (which normally contains the path to the executable being called).
  argv[0]=strdup(gcc);

  run(gcc, argv);
  
  // now do preprocessing call
  char **new_argv=malloc(sizeof(char *)*(argc+1));
  
  _Bool compile=0;
  _Bool assemble=0;
  _Bool next_is_o=0;
  
  unsigned i;

  for(i=0; i<argc; i++)
  {
    char *arg=argv[i];

    if(next_is_o)
    {
      char *tmp=malloc(strlen(arg)+strlen(".i"));
      strcpy(tmp, arg);
      unsigned l=strlen(tmp);

      if(strcmp(tmp+l-2, ".o")==0)
        tmp[l-2]=0; // cut off .o
      
      strcat(tmp, ".i"); // append .i
      arg=tmp;
      next_is_o=0;
    }
    else if(strcmp(arg, "-c")==0)
    {
      arg="-E";
      compile=1;
    }
    else if(strcmp(arg, "-o")==0)
    {
      next_is_o=1;
    }
    else if(strncmp(arg, "-", 1)!=0)
    {
      const char *ext=strrchr(arg, '.');
      if(ext!=NULL)
        if(strcmp(ext, ".S")==0 ||
           strcmp(ext, ".sx")==0 ||
           strcmp(ext, ".s")==0)
        {
          assemble=1;
        }
    }

    new_argv[i]=arg;
  }
  
  new_argv[argc]=NULL;
  
  if(compile && !assemble)
  {
    run(gcc, new_argv);
  }
    
  return 0;
}
