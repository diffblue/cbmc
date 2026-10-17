# Preprocess cbmc-cpp tests with the MSVC toolchain so that a failure on a
# Windows CI job can be reproduced elsewhere from the resulting .ii files:
# `cbmc --winx64 <flags from test.desc> test_X.ii'.
#
# usage: preprocess_cpp_tests.ps1 CBMC OUTDIR [TEST...]
#
# Preprocesses every test that test.pl's logs in regression\cbmc-cpp record
# as failed, and in addition each TEST given (for tests that were excluded,
# or that did not finish before ctest's timeout and so are not in the logs).

param(
  [Parameter(Mandatory = $true)][string]$Cbmc,
  [Parameter(Mandatory = $true)][string]$OutDir,
  [Parameter(ValueFromRemainingArguments = $true)][string[]]$Extra
)

$Cbmc = (Resolve-Path $Cbmc).Path
New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
$OutDir = (Resolve-Path $OutDir).Path
$root = Split-Path -Parent $PSScriptRoot

foreach ($hdr in @("tuple", "string_view", "variant", "any", "string", "map",
                   "optional", "vector", "list", "set", "thread", "mutex",
                   "filesystem", "chrono", "valarray", "iostream", "memory",
                   "functional", "sstream", "iomanip")) {
  $pp = Join-Path $OutDir "pp_$hdr.cpp"
  "#include <$hdr>`nint main() {}" | Set-Content $pp
  & $Cbmc --cpp17 --preprocess $pp 2>$null |
    Set-Content (Join-Path $OutDir "$hdr.ii")
  Remove-Item $pp
}

# test.pl's log: a "Test 'NAME'" block per test, "[FAILED]" lines within
$tests = @()
$current = ""
$logs = Get-ChildItem (Join-Path $root "regression\cbmc-cpp\tests*.log") `
  -ErrorAction SilentlyContinue
foreach ($line in ($logs | Get-Content)) {
  if ($line -match "^Test '([^']+)'") { $current = $Matches[1] }
  elseif ($line -match "\[FAILED\]" -and $current -ne "") { $tests += $current }
}
if ($Extra) { $tests += $Extra }
$tests = $tests | Sort-Object -Unique

foreach ($t in $tests) {
  $dir = Join-Path $root "regression\cbmc-cpp\$t"
  $desc = Join-Path $dir "test.desc"
  if (-not (Test-Path $desc)) { continue }
  $lines = Get-Content $desc
  $src = Join-Path $dir $lines[1].Trim()
  if (-not (Test-Path $src)) { continue }
  $flags = $lines[2].Trim().Split(" ", [StringSplitOptions]::RemoveEmptyEntries)
  Push-Location $dir
  & $Cbmc @flags --preprocess $src 2>$null |
    Set-Content (Join-Path $OutDir "test_$t.ii")
  Pop-Location
}
exit 0
