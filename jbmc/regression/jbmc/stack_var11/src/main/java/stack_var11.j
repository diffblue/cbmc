.class public stack_var11
.super java/lang/Object

.field private arr [I

.method public <init>()V
.limit stack 5
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   aload_0
   iconst_2
   newarray int
   putfield stack_var11/arr [I
   return
.end method

.method public f()I
   .limit stack 8
   .limit locals 5
   aload_0
   getfield stack_var11/arr [I
   iconst_0
   iaload ;; put arr[0] on stack (currently 0)
   aload_0
   getfield stack_var11/arr [I
   iconst_0
   iconst_1
   iastore ;; store 1 in arr[0],
           ;; value on stack should not be touched
   ireturn
.end method
