.class public Sync
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()V
Start:
   aload_0
   monitorexit
End:
   new java/lang/AssertionError
   dup
   invokespecial java/lang/AssertionError/<init>()V
   athrow
   return
Handle:
   return
.catch java/lang/IllegalMonitorStateException from Start to End using Handle
.end method
