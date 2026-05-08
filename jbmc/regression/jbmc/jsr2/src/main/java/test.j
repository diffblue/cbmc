; This is Jasmin assembler syntax-- see http://jasmin.sourceforge.net/guide.html or apt-get install jasmin-sable

.class public test
.super java/lang/Object

; standard initializer
.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public static main()V
   .limit locals 4
   .limit stack 1
  goto          runsrs
sr1:
  astore_0
  ret           0
runsrs:
  jsr           sr1
  jsr           sr2
  return
sr2:
  astore_3
  ret           3
.end method

