#!/usr/bin/env bash

# Fail on errors
# set -e # not for now

# Show steps we execute
set -x

# This script needs to operate in the root directory of the CBMC repository
SCRIPT=$(readlink -e "$0")
readonly SCRIPT
SCRIPTDIR=$(dirname "$SCRIPT")
readonly SCRIPTDIR
cd "$SCRIPTDIR/../.."

# Build CBMC tools
make -C src minisat2-download
make -C src CXX='ccache /usr/bin/g++' cbmc.dir goto-cc.dir goto-diff.dir -j$(nproc)

# Get one-line-scan, if we do not have it already
[ -d one-line-scan ] || git clone https://github.com/awslabs/one-line-scan.git one-line-scan

# Get Linux v5.10, if we do not have it already
[ -d linux_5_10 ] || git clone -b v5.10 --depth=1 https://github.com/torvalds/linux/ linux_5_10

# Prepare compile a part of the kernel with CBMC via one-line-scan
ln -s goto-cc src/goto-cc/goto-ld
ln -s goto-cc src/goto-cc/goto-as
ln -s goto-cc src/goto-cc/goto-g++


configure_linux ()
{
  pushd linux_5_10
  # GCC >= 12 correctly reports (and fails with) use-after-free, which was
  # eventually fixed in 5.16.11 (and 5.17+)
  curl https://github.com/torvalds/linux/commit/52a9dab6d892763b2a8334a568bd4e2c1a6fde66.patch | patch -p1
  # Some versions of binutils fail to generate a symbol table, pick up fix that
  # eventually landed in 6.0, see
  # https://github.com/torvalds/linux/commit/de979c83574abf6e78f3fa65b716515c91b2613d
  cat > de979c83574abf6e78f3fa65b716515c91b2613d-adjusted.patch << "EOF"
diff --git a/arch/x86/entry/Makefile b/arch/x86/entry/Makefile
index 08bf95dbc..83c98dae7 100644
--- a/arch/x86/entry/Makefile
+++ b/arch/x86/entry/Makefile
@@ -21,12 +21,13 @@ CFLAGS_syscall_64.o		+= $(call cc-option,-Wno-override-init,)
 CFLAGS_syscall_32.o		+= $(call cc-option,-Wno-override-init,)
 CFLAGS_syscall_x32.o		+= $(call cc-option,-Wno-override-init,)
 
-obj-y				:= entry_$(BITS).o thunk_$(BITS).o syscall_$(BITS).o
+obj-y				:= entry_$(BITS).o syscall_$(BITS).o
 obj-y				+= common.o
 
 obj-y				+= vdso/
 obj-y				+= vsyscall/
 
+obj-$(CONFIG_PREEMPTION)	+= thunk_$(BITS).o
 obj-$(CONFIG_IA32_EMULATION)	+= entry_64_compat.o syscall_32.o
 obj-$(CONFIG_X86_X32_ABI)	+= syscall_x32.o
 
diff --git a/arch/x86/entry/thunk_32.S b/arch/x86/entry/thunk_32.S
index f1f96d4d8..5997ec0b4 100644
--- a/arch/x86/entry/thunk_32.S
+++ b/arch/x86/entry/thunk_32.S
@@ -29,10 +29,8 @@ SYM_CODE_START_NOALIGN(\name)
 SYM_CODE_END(\name)
 	.endm
 
-#ifdef CONFIG_PREEMPTION
 	THUNK preempt_schedule_thunk, preempt_schedule
 	THUNK preempt_schedule_notrace_thunk, preempt_schedule_notrace
 	EXPORT_SYMBOL(preempt_schedule_thunk)
 	EXPORT_SYMBOL(preempt_schedule_notrace_thunk)
-#endif
 
diff --git a/arch/x86/entry/thunk_64.S b/arch/x86/entry/thunk_64.S
index ccd32877a..c7cf79be7 100644
--- a/arch/x86/entry/thunk_64.S
+++ b/arch/x86/entry/thunk_64.S
@@ -36,14 +36,11 @@ SYM_FUNC_END(\name)
 	_ASM_NOKPROBE(\name)
 	.endm
 
-#ifdef CONFIG_PREEMPTION
 	THUNK preempt_schedule_thunk, preempt_schedule
 	THUNK preempt_schedule_notrace_thunk, preempt_schedule_notrace
 	EXPORT_SYMBOL(preempt_schedule_thunk)
 	EXPORT_SYMBOL(preempt_schedule_notrace_thunk)
-#endif
 
-#ifdef CONFIG_PREEMPTION
 SYM_CODE_START_LOCAL_NOALIGN(.L_restore)
 	popq %r11
 	popq %r10
@@ -58,4 +55,3 @@ SYM_CODE_START_LOCAL_NOALIGN(.L_restore)
 	ret
 	_ASM_NOKPROBE(.L_restore)
 SYM_CODE_END(.L_restore)
-#endif
diff --git a/arch/x86/um/Makefile b/arch/x86/um/Makefile
index 77f70b969..3113800da 100644
--- a/arch/x86/um/Makefile
+++ b/arch/x86/um/Makefile
@@ -27,7 +27,8 @@ else
 
 obj-y += syscalls_64.o vdso/
 
-subarch-y = ../lib/csum-partial_64.o ../lib/memcpy_64.o ../entry/thunk_64.o
+subarch-y = ../lib/csum-partial_64.o ../lib/memcpy_64.o
+subarch-$(CONFIG_PREEMPTION) += ../entry/thunk_64.o
 
 endif
 
EOF
  patch -p1 < de979c83574abf6e78f3fa65b716515c91b2613d-adjusted.patch

  cat > kvm-config <<EOF
CONFIG_64BIT=y
CONFIG_X86_64=y
CONFIG_HIGH_RES_TIMERS=y
CONFIG_MULTIUSER=y
CONFIG_NET=y
CONFIG_VIRTUALIZATION=y
CONFIG_HYPERVISOR_GUEST=y
CONFIG_PARAVIRT=y
CONFIG_KVM_GUEST=y
CONFIG_KVM=y
CONFIG_KVM_INTEL=y
CONFIG_KVM_AMD=y
EOF
  # use the configuration from the generated file
  export KCONFIG_ALLCONFIG=kvm-config

  # ... and use it during configuration
  make allnoconfig
  popd
}

# Configure kernel, and compile all of it
configure_linux
make -C linux_5_10 bzImage -j $(nproc)

# Clean files we want to be able to re-compile
find linux_5_10/arch/x86/kvm/ -name "*.o" -delete

# Compile Linux with CBMC via one-line-scan, and check for goto-cc section
# Re-Compile with goto-cc, and measure disk space
declare -i STATUS=0
du -h --max-depth=1
one-line-scan/one-line-scan \
    --add-to-path $(pwd)/src/cbmc --add-to-path $(pwd)/src/goto-diff --add-to-path $(pwd)/src/goto-cc \
    --cbmc \
    --no-analysis \
    --trunc-existing \
    --extra-cflags -Wno-error \
    -o CPROVER -j 5 -- \
    make -C linux_5_10 bzImage -j $(nproc) || STATUS=$?
du -h --max-depth=1

# Check for faulty input
ls CPROVER/faultyInput/* || true

# Check for produced output in the files we deleted above
objdump -h linux_5_10/arch/x86/kvm/x86.o | grep "goto-cc" || STATUS=$?

# Propagate failures
exit "$STATUS"
