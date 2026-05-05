.class public stack_var6
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f(III)I
   .limit stack 8
   .limit locals 5

   ;; push local var3 / var2 / var1
   iload_1
   iload_2
   iload_3
   dup2_x1
   ;; add one to local var 2
   iinc 2 1
   ;; sub
   isub
   ;; incremented copy on stack
   ireturn
.end method
