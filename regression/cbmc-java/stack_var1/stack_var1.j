.class public stack_var1
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f(I)I
   .limit stack 2
   .limit locals 2

   ;; copy of arg on stack
   iload_1
   ;; increment arg
   iinc 1 1
   ;; incremented copy on stack
   iload_1
   isub
   ireturn
.end method
