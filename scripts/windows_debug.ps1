# TEMPORARY DEBUG (Windows CI investigation): collect what a Windows build
# of cbmc does differently for tests that fail only there.
#
# usage: windows_debug.ps1 CBMC OUTDIR
#
# For each test below, OUTDIR\<test> receives
#   main.ii       the test's source preprocessed by cl (cbmc --preprocess)
#   run.txt       a run with the test's options, --verbosity 9 and --trace
#   goto.txt      --show-goto-functions
#   symbols.txt   --show-symbol-table
#   library\      the C library models before and after preprocessing
#                 (CBMC_DUMP_PREPROCESSED_DIR, see c_preprocess.cpp)
# plus probes: small programs checking the C library models directly.

param(
  [Parameter(Mandatory = $true)][string]$Cbmc,
  [Parameter(Mandatory = $true)][string]$OutDir
)

$Cbmc = (Resolve-Path $Cbmc).Path
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
$OutDir = (Resolve-Path $OutDir).Path
$root = Split-Path -Parent $PSScriptRoot

function Run-Cbmc($Dir, $Arguments, $File) {
  Push-Location $Dir
  & $Cbmc @Arguments 2>&1 | Out-File -Encoding utf8 $File
  "EXIT=$LastExitCode" | Out-File -Append -Encoding utf8 $File
  Pop-Location
}

function Collect($Test, $Desc, $ExtraFlags) {
  $dir = Join-Path $root "regression\cbmc-cpp\$Test"
  $lines = Get-Content (Join-Path $dir $Desc)
  $src = $lines[1].Trim()
  $flags = @($lines[2].Trim().Split(" ", [StringSplitOptions]::RemoveEmptyEntries))
  $out = Join-Path $OutDir "$Test-$Desc"
  New-Item -ItemType Directory -Force -Path (Join-Path $out "library") | Out-Null
  Copy-Item (Join-Path $dir $Desc) $out
  Run-Cbmc $dir ($flags + @("--preprocess", $src)) (Join-Path $out "main.ii")
  $env:CBMC_DUMP_PREPROCESSED_DIR = Join-Path $out "library"
  Run-Cbmc $dir ($flags + $ExtraFlags + @("--verbosity", "9", "--trace", $src)) `
    (Join-Path $out "run.txt")
  Remove-Item Env:\CBMC_DUMP_PREPROCESSED_DIR
  Run-Cbmc $dir ($flags + @("--show-goto-functions", $src)) (Join-Path $out "goto.txt")
  Run-Cbmc $dir ($flags + @("--show-symbol-table", $src)) (Join-Path $out "symbols.txt")
}

# memcpy source region readable: FAILURE in _Impl_copy_memmeow_tail
Collect "cpp11_vector_probe" "test.desc" @()
Collect "cpp20_erase_if" "test.desc" @()
# invariant: fgetc type inconsistency (goto_program.cpp, __msvc_filebuf.hpp)
Collect "cpp11_out_of_line_defaulted_member_of_class_template" "test_libstdcxx.desc" @()
# parse error before 'alignas ( _Loop_vals_v3_t <' in <regex>
Collect "cpp11_default_member_initializer_array_of_class_from_nested_braces" "test_libstdcxx.desc" @()

# Probes of the C library models (memcpy's preconditions; fgetc's type)
$probes = Join-Path $OutDir "probes"
New-Item -ItemType Directory -Force -Path (Join-Path $probes "library") | Out-Null
@'
#include <string.h>
int main()
{
  char a[4] = {1, 2, 3, 4};
  char b[4];
  memcpy(b, a, 4);
  __CPROVER_assert(b[3] == 4, "copied");
  __CPROVER_assert(b[3] == 5, "WRONG (must FAIL)");
  return 0;
}
'@ | Set-Content (Join-Path $probes "memcpy.c")
@'
#include <stdio.h>
int main()
{
  int c = fgetc(stdin);
  __CPROVER_assert(c >= -1, "fgetc");
  return 0;
}
'@ | Set-Content (Join-Path $probes "fgetc.c")
@'
#include <cstring>
int main()
{
  char a[4] = {1, 2, 3, 4};
  char b[4];
  std::memcpy(b, a, 4);
  __CPROVER_assert(b[3] == 4, "copied");
  return 0;
}
'@ | Set-Content (Join-Path $probes "memcpy.cpp")
$env:CBMC_DUMP_PREPROCESSED_DIR = Join-Path $probes "library"
foreach ($p in @("memcpy.c", "fgetc.c", "memcpy.cpp")) {
  Run-Cbmc $probes @("--pointer-check", "--verbosity", "9", "--trace", $p) `
    (Join-Path $probes "$p.run.txt")
  Run-Cbmc $probes @("--show-goto-functions", $p) (Join-Path $probes "$p.goto.txt")
}
Remove-Item Env:\CBMC_DUMP_PREPROCESSED_DIR
exit 0
