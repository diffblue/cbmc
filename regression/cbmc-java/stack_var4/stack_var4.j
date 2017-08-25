.class public stack_var4
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()I
   .limit stack 5
   .limit locals 4

   ;; 0->var1
   ;; 1->var2
   ;; 2->var3
   iconst_0
   istore_1
   iconst_1
   istore_2
   iconst_2
   istore_3

   ;; push local var3 / var2 / var1
   iload_3
   iload_2
   iload_1
   ;; push var1 in front of var3
   dup_x2
   ;; add one to local var 1
   iinc 1 1
   pop
   pop
   pop
   ;; incremented copy on stack
   ireturn
.end method
