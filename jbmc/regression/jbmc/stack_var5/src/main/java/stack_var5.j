.class public stack_var5
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()I
   .limit stack 4
   .limit locals 4

   ;; 1->var1
   ;; 2->var2
   iconst_1
   istore_1
   iconst_2
   istore_2

   ;; push local var2 / var1
   iload_2
   iload_1

   ;; duplicate var2 / var1
   dup2
   ;; add one to local var 1
   iinc 1 1
   ;; sub
   isub
   ;; incremented copy on stack
   ireturn
.end method
