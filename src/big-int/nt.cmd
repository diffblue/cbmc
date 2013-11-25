rem $Id: nt.cmd,v 1.1.1.1 2002-06-13 22:00:30 kroening Exp $
rem
rem Compile bigint class and run test program.

set CFLAGS=-Gr -GR- -GX- -Gi- -Gm- -G6 -W3
set OPTIMIZE=-Ox

cl %CFLAGS% %OPTIMIZE% -Fe"bigint-test" -TP bigint-test.cc bigint.cc bigint-func.cc
bigint-test.exe
