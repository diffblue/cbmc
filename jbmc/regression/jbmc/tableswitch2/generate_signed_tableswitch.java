import org.objectweb.asm.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.Path;
import java.io.IOException;

public class generate_signed_tableswitch
{
  void doIt() throws IOException
  {
    ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_MAXS);

    cw.visit(Opcodes.V1_7, Opcodes.ACC_PUBLIC, "table_switch_neg_offset",
             null, "java/lang/Object", null);
    {
      MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PUBLIC, "f", "()V", null, null);
      Label fwdJump = new Label();
      Label backJump = new Label();
      Label defaultLabel = new Label();

      mv.visitCode();
      mv.visitJumpInsn(Opcodes.GOTO, fwdJump);
      mv.visitLabel(backJump);
      mv.visitInsn(Opcodes.RETURN);
      mv.visitLabel(fwdJump);
      mv.visitInsn(Opcodes.ICONST_0);
      mv.visitTableSwitchInsn(0, 0, defaultLabel, new Label[]{backJump});
      mv.visitLabel(defaultLabel);
      mv.visitInsn(Opcodes.RETURN);
      mv.visitMaxs(1, 1);
      mv.visitEnd();
    }
    cw.visitEnd();
    Path path = Paths.get("table_switch_neg_offset.class");
    Files.write(path, cw.toByteArray());
  }

  public static void main(String[] args) throws IOException
  {
    new generate_signed_tableswitch().doIt();
  }
}
