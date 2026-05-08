.class public stack_var7
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()I
   .limit stack 8
   .limit locals 5

   ;; 1->var1
   ;; 2->var2
   ;; 4->var3
   ;; 8->var4
   iconst_1
   istore_1
   iconst_2
   istore_2
   iconst_4
   istore_3
   bipush 8
   istore 4
   ;; push local var4 / var3 / var2 / var1
   iload 4
   iload_3
   iload_2
   iload 1
   ;; push var2 / var1 in on head
   dup2_x2
   ;; add one to local var 1
   iinc 1 1
   pop
   pop
   pop
   pop
   ;; sub
   isub
   ;; incremented copy on stack
   ireturn
.end method
