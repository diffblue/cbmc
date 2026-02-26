#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Evaluate CBMC proofs from mlkem-native and mldsa-native with different
# solver backends (Z3/SMT, MiniSat/SAT, CaDiCaL/SAT) and compare results.
#
# Usage:
#   ./scripts/run_pqc_proofs.sh [OPTIONS]
#
# Options:
#   --cbmc-dir DIR       Path to CBMC build directory (default: build under repo root)
#   --work-dir DIR       Working directory for clones and results (default: /tmp/pqc-proofs)
#   --timeout SECS       Per-proof CBMC timeout in seconds (default: 600)
#   --proofs PATTERN     Only run proofs matching PATTERN (grep -E)
#   --repos REPOS        Comma-separated list: mlkem,mldsa (default: both)
#   --skip-clone         Don't clone repos (assume they exist in work-dir)
#   --skip-build         Don't rebuild goto binaries (assume they exist)
#   --jobs N             Parallel proof builds via litani (default: 1)
#   --parallel N         Run N proofs in parallel (default: 1)
#   --install-deps       Auto-install Z3 4.15.3 and latest Bitwuzla into <work-dir>/tools
#   --memlimit MB        Per-proof virtual memory limit in MB (default: 85% of system RAM)
#   -h, --help           Show this help

set -euo pipefail

########################################################################
# Defaults
########################################################################

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CBMC_DIR="${REPO_ROOT}/build/bin"
WORK_DIR="/tmp/pqc-proofs"
TIMEOUT=600
PROOF_PATTERN=""
REPOS="mlkem,mldsa"
SKIP_CLONE=false
SKIP_BUILD=false
INSTALL_DEPS=false
JOBS=1
PARALLEL=1
MEMLIMIT_KB=""

########################################################################
# Parse arguments
########################################################################

while [[ $# -gt 0 ]]; do
  case "$1" in
    --cbmc-dir)   CBMC_DIR="$2"; shift 2;;
    --work-dir)   WORK_DIR="$2"; shift 2;;
    --timeout)    TIMEOUT="$2"; shift 2;;
    --proofs)     PROOF_PATTERN="$2"; shift 2;;
    --repos)      REPOS="$2"; shift 2;;
    --skip-clone) SKIP_CLONE=true; shift;;
    --skip-build) SKIP_BUILD=true; shift;;
    --install-deps) INSTALL_DEPS=true; shift;;
    --memlimit)   MEMLIMIT_KB=$(( $2 * 1024 )); shift 2;;
    --jobs)       JOBS="$2"; shift 2;;
    --parallel)   PARALLEL="$2"; shift 2;;
    -h|--help)
      sed -n '2,/^$/{ s/^# \?//; p }' "$0"
      exit 0;;
    *) echo "Unknown option: $1" >&2; exit 1;;
  esac
done

########################################################################
# Tool checks
########################################################################

CBMC="${CBMC_DIR}/cbmc"
GOTO_CC="${CBMC_DIR}/goto-cc"
GOTO_INSTRUMENT="${CBMC_DIR}/goto-instrument"
CRANGLER="${CBMC_DIR}/crangler"

fail() { echo "ERROR: $*" >&2; exit 1; }

########################################################################
# Auto-install Z3 and Bitwuzla (--install-deps)
########################################################################

install_deps() {
  local tools_dir="${WORK_DIR}/tools"
  local bin_dir="${tools_dir}/bin"
  mkdir -p "$bin_dir"

  local arch
  arch="$(uname -m)"
  local os
  os="$(uname -s)"

  if [[ "$os" != "Linux" ]]; then
    fail "--install-deps currently only supports Linux"
  fi

  # --- Z3 4.15.3 ---
  local z3_bin="${bin_dir}/z3"
  if [[ -x "$z3_bin" ]] && "$z3_bin" --version 2>&1 | grep -q '4\.15\.3'; then
    echo "Z3 4.15.3 already installed at $z3_bin"
  else
    echo "Installing Z3 4.15.3..."
    local z3_asset z3_dir_name
    case "$arch" in
      x86_64)  z3_asset="z3-4.15.3-x64-glibc-2.39.zip"; z3_dir_name="z3-4.15.3-x64-glibc-2.39";;
      aarch64) z3_asset="z3-4.15.3-arm64-glibc-2.34.zip"; z3_dir_name="z3-4.15.3-arm64-glibc-2.34";;
      *) fail "Unsupported architecture for Z3: $arch";;
    esac
    local z3_url="https://github.com/Z3Prover/z3/releases/download/z3-4.15.3/${z3_asset}"
    local z3_tmp="${tools_dir}/z3_download"
    rm -rf "$z3_tmp"
    mkdir -p "$z3_tmp"
    echo "  Downloading $z3_url"
    curl -sL "$z3_url" -o "${z3_tmp}/${z3_asset}"
    unzip -q -o "${z3_tmp}/${z3_asset}" -d "$z3_tmp"
    cp "${z3_tmp}/${z3_dir_name}/bin/z3" "$z3_bin"
    chmod +x "$z3_bin"
    # Also copy libz3.so next to the binary so z3 can find it
    cp "${z3_tmp}/${z3_dir_name}/bin/libz3.so" "${bin_dir}/" 2>/dev/null || true
    rm -rf "$z3_tmp"
    echo "  Installed: $("$z3_bin" --version 2>&1)"
  fi

  # --- Bitwuzla (latest release) ---
  local bw_bin="${bin_dir}/bitwuzla"
  if [[ -x "$bw_bin" ]]; then
    echo "Bitwuzla already installed at $bw_bin"
  else
    echo "Installing Bitwuzla (latest release)..."
    local bw_asset bw_dir_name
    case "$arch" in
      x86_64)  bw_asset="Bitwuzla-Linux-x86_64-static.zip"; bw_dir_name="Bitwuzla-Linux-x86_64-static";;
      aarch64) bw_asset="Bitwuzla-Linux-arm64-static.zip"; bw_dir_name="Bitwuzla-Linux-arm64-static";;
      *) fail "Unsupported architecture for Bitwuzla: $arch";;
    esac
    local bw_url="https://github.com/bitwuzla/bitwuzla/releases/latest/download/${bw_asset}"
    local bw_tmp="${tools_dir}/bw_download"
    rm -rf "$bw_tmp"
    mkdir -p "$bw_tmp"
    echo "  Downloading $bw_url"
    curl -sL "$bw_url" -o "${bw_tmp}/${bw_asset}"
    unzip -q -o "${bw_tmp}/${bw_asset}" -d "$bw_tmp"
    cp "${bw_tmp}/${bw_dir_name}/bin/bitwuzla" "$bw_bin"
    chmod +x "$bw_bin"
    rm -rf "$bw_tmp"
    echo "  Installed: $("$bw_bin" --version 2>&1)"
  fi

  # Prepend tools/bin to PATH so the rest of the script finds them
  export PATH="${bin_dir}:${PATH}"
  export LD_LIBRARY_PATH="${bin_dir}:${LD_LIBRARY_PATH:-}"
}

if [[ "$INSTALL_DEPS" == true ]]; then
  mkdir -p "$WORK_DIR"
  install_deps
  echo ""
fi

[[ -x "$CBMC" ]]             || fail "cbmc not found at $CBMC"
[[ -x "$GOTO_CC" ]]          || fail "goto-cc not found at $GOTO_CC"
[[ -x "$GOTO_INSTRUMENT" ]]  || fail "goto-instrument not found at $GOTO_INSTRUMENT"
[[ -x "$CRANGLER" ]]          || fail "crangler not found at $CRANGLER"
command -v litani >/dev/null  || fail "litani not found in PATH"
command -v z3 >/dev/null      || fail "z3 not found in PATH (install Z3 >= 4.13)"
command -v /usr/bin/time >/dev/null || fail "/usr/bin/time not found"

HAS_BITWUZLA=false
if command -v bitwuzla >/dev/null 2>&1; then
  HAS_BITWUZLA=true
fi

CBMC_VERSION="$("$CBMC" --version 2>&1 | head -1)"
Z3_VERSION="$(z3 --version 2>&1)"
BITWUZLA_VERSION="(not installed)"
if $HAS_BITWUZLA; then
  BITWUZLA_VERSION="$(bitwuzla --version 2>&1)"
fi

echo "=== Tool versions ==="
echo "CBMC:      $CBMC_VERSION"
echo "Z3:        $Z3_VERSION"
echo "Bitwuzla:  $BITWUZLA_VERSION"
echo "Litani:    $(litani --version 2>&1)"
echo ""

if ! $HAS_BITWUZLA; then
  echo "WARNING: bitwuzla not found in PATH. Proofs that use --bitwuzla will"
  echo "         skip the original-backend SMT run. Install bitwuzla to enable."
  echo ""
fi

# Check Z3 version is recent enough (>= 4.13)
z3_minor=$(echo "$Z3_VERSION" | grep -oP 'version \K[0-9]+\.[0-9]+' | cut -d. -f2)
z3_major=$(echo "$Z3_VERSION" | grep -oP 'version \K[0-9]+' | head -1)
if [[ "$z3_major" -lt 4 ]] || { [[ "$z3_major" -eq 4 ]] && [[ "$z3_minor" -lt 13 ]]; }; then
  echo "WARNING: Z3 version >= 4.13 recommended (found: $Z3_VERSION)."
  echo "         SMT proofs may fail or produce different results with older Z3."
  echo ""
fi

########################################################################
# Clone repositories
########################################################################

mkdir -p "$WORK_DIR"
RESULTS_DIR="${WORK_DIR}/results"
mkdir -p "$RESULTS_DIR"

clone_repo() {
  local name="$1" url="$2" dest="${WORK_DIR}/$1"
  if [[ "$SKIP_CLONE" == true ]] && [[ -d "$dest" ]]; then
    echo "Reusing existing clone: $dest"
    return
  fi
  echo "Cloning $url -> $dest"
  rm -rf "$dest"
  git clone --depth 1 "$url" "$dest"
}

if [[ "$REPOS" == *mlkem* ]]; then
  clone_repo mlkem-native https://github.com/pq-code-package/mlkem-native.git
fi
if [[ "$REPOS" == *mldsa* ]]; then
  clone_repo mldsa-native https://github.com/pq-code-package/mldsa-native.git
fi

########################################################################
# Discover proofs
########################################################################

# list_proofs <repo-dir> -> prints proof directory names, one per line
list_proofs() {
  local repo_dir="$1"
  ls -1 "${repo_dir}"/proofs/cbmc/**/*harness.c 2>/dev/null \
    | xargs -I{} dirname {} \
    | xargs -I{} basename {} \
    | sort -u
}

########################################################################
# Extract CBMC flags from a proof Makefile
########################################################################

# Parses the proof Makefile to extract the non-backend CBMCFLAGS and
# other relevant settings.  Returns shell variables via eval.
#
# Output variables:
#   PROOF_BACKEND        - original backend (smt2, bitwuzla, cvc5, external-smt2, or empty)
#   PROOF_EXTRA_FLAGS    - CBMCFLAGS minus the backend selector
#   PROOF_OBJECT_BITS    - --object-bits N
#   PROOF_HARNESS_FILE   - harness file basename (without .c)
extract_proof_config() {
  local makefile="$1"
  local proof_root
  proof_root="$(dirname "$(dirname "$makefile")")"

  # Read all CBMCFLAGS lines (both = and +=)
  local all_flags=""
  while IFS= read -r line; do
    # Handle both CBMCFLAGS= and CBMCFLAGS+=
    local val
    val="$(echo "$line" | sed 's/^[[:space:]]*CBMCFLAGS[[:space:]]*+\?=[[:space:]]*//')"
    all_flags="$all_flags $val"
  done < <(grep '^[[:space:]]*CBMCFLAGS' "$makefile" | grep -v '^[[:space:]]*#')

  # Determine backend
  local backend=""
  if echo "$all_flags" | grep -q -- '--external-smt2-solver'; then
    backend="external-smt2"
  elif echo "$all_flags" | grep -q -- '--bitwuzla'; then
    backend="bitwuzla"
  elif echo "$all_flags" | grep -q -- '--cvc5'; then
    backend="cvc5"
  elif echo "$all_flags" | grep -q -- '--smt2'; then
    backend="smt2"
  fi

  # Strip backend flags to get extra flags
  local extra
  extra="$(echo "$all_flags" \
    | sed 's/--external-smt2-solver[[:space:]]*[^[:space:]]*//' \
    | sed 's/--bitwuzla//' \
    | sed 's/--cvc5//' \
    | sed 's/--smt2//' \
    | sed 's/--z3//' \
    | sed 's/[[:space:]]\+/ /g' \
    | sed 's/^ *//;s/ *$//')"

  # Object bits
  local obj_bits
  obj_bits="$(grep 'CBMC_OBJECT_BITS' "$makefile" | grep -v '#' | tail -1 | sed 's/.*=[[:space:]]*//' | tr -d '[:space:]')"
  [[ -z "$obj_bits" ]] && obj_bits=8

  # Harness file
  local harness_file
  harness_file="$(grep 'HARNESS_FILE' "$makefile" | grep -v '#' | head -1 | sed 's/.*=[[:space:]]*//' | tr -d '[:space:]')"

  echo "PROOF_BACKEND='$backend'"
  echo "PROOF_EXTRA_FLAGS='$extra'"
  echo "PROOF_OBJECT_BITS='$obj_bits'"
  echo "PROOF_HARNESS_FILE='$harness_file'"
}

########################################################################
# Build goto binaries
########################################################################

# build_goto <repo-dir> <proof-name> <param-var> <param-val>
build_goto() {
  local repo_dir="$1" proof="$2" param_var="$3" param_val="$4"
  local proof_dir="${repo_dir}/proofs/cbmc/${proof}"

  if [[ "$SKIP_BUILD" == true ]]; then
    local harness_file
    harness_file="$(grep 'HARNESS_FILE' "${proof_dir}/Makefile" | grep -v '#' | head -1 | sed 's/.*=[[:space:]]*//' | tr -d '[:space:]')"
    if [[ -f "${proof_dir}/gotos/${harness_file}.goto" ]]; then
      return 0
    fi
    echo "  WARNING: --skip-build but goto binary missing for $proof, building..."
  fi

  (
    cd "$proof_dir"
    make -s veryclean 2>/dev/null || true
    make goto \
      "${param_var}=${param_val}" \
      CBMC="$CBMC" \
      GOTO_CC="$GOTO_CC" \
      GOTO_INSTRUMENT="$GOTO_INSTRUMENT" \
      CRANGLER="$CRANGLER" \
      2>&1
  )
}

########################################################################
# Run CBMC with a given backend and capture results
########################################################################

# run_cbmc_backend <goto-file> <backend-args> <extra-flags> <object-bits> <timeout> <output-prefix>
#
# Writes:
#   <output-prefix>.stdout   - CBMC stdout
#   <output-prefix>.stderr   - CBMC stderr
#   <output-prefix>.time     - /usr/bin/time output (wall time, max RSS)
#   <output-prefix>.meta     - exit_code, result, wall_time_s, max_rss_kb
run_cbmc_backend() {
  local goto_file="$1" backend_args="$2" extra_flags="$3" object_bits="$4" timeout="$5" out_prefix="$6"

  # Build the CBMC command.  The standard CHECKFLAGS from Makefile.common are:
  #   --conversion-check --float-overflow-check --nan-check
  #   --pointer-overflow-check --unsigned-overflow-check
  #   --malloc-may-fail --malloc-fail-null
  # We replicate them here so the SAT run uses the same checks as the SMT run.
  local -a cmd=(
    "$CBMC"
    --object-bits "$object_bits"
    --flush
  )

  # Add backend-specific args (may be empty for default SAT)
  if [[ -n "$backend_args" ]]; then
    # shellcheck disable=SC2206
    cmd+=($backend_args)
  fi

  # Add extra flags from the proof Makefile (e.g. --no-array-field-sensitivity)
  if [[ -n "$extra_flags" ]]; then
    # shellcheck disable=SC2206
    cmd+=($extra_flags)
  fi

  # Standard check flags (matching Makefile.common defaults)
  cmd+=(
    --conversion-check
    --float-overflow-check
    --nan-check
    --pointer-overflow-check
    --unsigned-overflow-check
    --malloc-may-fail --malloc-fail-null
    --trace
    "$goto_file"
  )

  local exit_code=0
  (
    # Apply soft virtual-memory limit inside a subshell
    if [[ -n "${MEMLIMIT_KB:-}" ]] && [[ "$MEMLIMIT_KB" -gt 0 ]]; then
      ulimit -v "$MEMLIMIT_KB" 2>/dev/null || true
    fi
    /usr/bin/time -v -o "${out_prefix}.time" \
      timeout "$timeout" \
      "${cmd[@]}" \
      >"${out_prefix}.stdout" 2>"${out_prefix}.stderr"
  ) || exit_code=$?

  # Parse result
  local result="UNKNOWN"
  if [[ $exit_code -eq 124 ]] || [[ $exit_code -eq 137 ]]; then
    result="TIMEOUT"
  elif grep -qi 'cannot allocate memory\|out of memory\|bad_alloc\|std::bad_alloc' "${out_prefix}.stderr" "${out_prefix}.stdout" 2>/dev/null; then
    result="OOM"
  elif grep -q 'VERIFICATION SUCCESSFUL' "${out_prefix}.stdout"; then
    result="SUCCESS"
  elif grep -q 'VERIFICATION FAILED' "${out_prefix}.stdout"; then
    result="FAILURE"
  elif grep -q 'VERIFICATION INCONCLUSIVE' "${out_prefix}.stdout"; then
    result="INCONCLUSIVE"
  elif grep -qi 'invariant' "${out_prefix}.stderr" || grep -qi 'invariant' "${out_prefix}.stdout"; then
    result="INVARIANT_VIOLATION"
  elif grep -qi 'error' "${out_prefix}.stderr"; then
    result="ERROR"
  fi

  # Parse timing (from /usr/bin/time -v output)
  local wall_time_s="N/A" max_rss_kb="N/A"
  if [[ -f "${out_prefix}.time" ]]; then
    wall_time_s="$(grep 'Elapsed (wall clock)' "${out_prefix}.time" \
      | sed 's/.*: //' \
      | awk -F: '{ if (NF==3) print $1*3600+$2*60+$3; else if (NF==2) print $1*60+$2; else print $1 }')" || true
    max_rss_kb="$(grep 'Maximum resident' "${out_prefix}.time" \
      | sed 's/.*: //')" || true
  fi

  cat > "${out_prefix}.meta" <<EOF
exit_code=${exit_code}
result=${result}
wall_time_s=${wall_time_s}
max_rss_kb=${max_rss_kb}
EOF
  echo "cmd=${cmd[*]}" >> "${out_prefix}.meta"
}

########################################################################
# Process one proof
########################################################################

# process_proof <repo-name> <repo-dir> <proof-name> <param-var> <param-val>
process_proof() {
  local repo_name="$1" repo_dir="$2" proof="$3" param_var="$4" param_val="$5"
  local proof_dir="${repo_dir}/proofs/cbmc/${proof}"
  local result_base="${RESULTS_DIR}/${repo_name}/${proof}"
  mkdir -p "$result_base"

  echo "--- ${repo_name}/${proof} ---"

  # Extract proof config
  local PROOF_BACKEND PROOF_EXTRA_FLAGS PROOF_OBJECT_BITS PROOF_HARNESS_FILE
  eval "$(extract_proof_config "${proof_dir}/Makefile")"

  local goto_file="${proof_dir}/gotos/${PROOF_HARNESS_FILE}.goto"

  # Build goto binary
  echo "  Building goto binary..."
  if ! build_goto "$repo_dir" "$proof" "$param_var" "$param_val" \
       > "${result_base}/build.log" 2>&1; then
    echo "  BUILD FAILED (see ${result_base}/build.log)"
    echo "build_result=FAILED" > "${result_base}/build.meta"
    return
  fi
  echo "build_result=OK" > "${result_base}/build.meta"

  if [[ ! -f "$goto_file" ]]; then
    echo "  ERROR: goto binary not found at $goto_file"
    echo "build_result=MISSING_GOTO" > "${result_base}/build.meta"
    return
  fi

  # Determine original SMT backend args
  local original_backend_args=""
  case "$PROOF_BACKEND" in
    smt2)           original_backend_args="--smt2";;
    bitwuzla)       original_backend_args="--bitwuzla";;
    cvc5)           original_backend_args="--cvc5";;
    external-smt2)
      # Re-read the raw external solver command from the Makefile
      local ext_solver_line
      ext_solver_line="$(grep -- '--external-smt2-solver' "${proof_dir}/Makefile" | head -1 | sed 's/.*CBMCFLAGS[[:space:]]*+\?=[[:space:]]*//')"
      # Resolve $(PROOF_ROOT) to actual path
      local proof_root
      proof_root="$(dirname "$proof_dir")"
      ext_solver_line="$(echo "$ext_solver_line" | sed "s|\$(PROOF_ROOT)|${proof_root}|g")"
      # Extract just the backend part (--external-smt2-solver ... --z3 or similar)
      original_backend_args="$(echo "$ext_solver_line" \
        | grep -oP -- '--external-smt2-solver\s+\S+(\s+--z3)?' )"
      ;;
  esac

  # Determine the number of runs for progress display
  local has_nafs=false
  if echo "$PROOF_EXTRA_FLAGS" | grep -q -- '--no-array-field-sensitivity'; then
    has_nafs=true
  fi
  local n_runs=3
  $has_nafs && n_runs=5

  # Run 1: Original SMT backend
  local skip_smt=false
  if [[ "$PROOF_BACKEND" == "bitwuzla" ]] && ! $HAS_BITWUZLA; then
    echo "  [1/${n_runs}] SKIPPED original backend (bitwuzla not installed)"
    cat > "${result_base}/smt.meta" <<SKIP_EOF
exit_code=N/A
result=SKIPPED
wall_time_s=N/A
max_rss_kb=N/A
cmd=skipped (bitwuzla not installed)
SKIP_EOF
    skip_smt=true
  fi
  if ! $skip_smt; then
    echo "  [1/${n_runs}] Running with original backend (${PROOF_BACKEND:-default})..."
    run_cbmc_backend "$goto_file" "$original_backend_args" "$PROOF_EXTRA_FLAGS" \
      "$PROOF_OBJECT_BITS" "$TIMEOUT" "${result_base}/smt"
  fi

  # Run 2: SAT with CaDiCaL (default SAT solver in this build)
  echo "  [2/${n_runs}] Running with CaDiCaL SAT backend..."
  run_cbmc_backend "$goto_file" "--sat-solver cadical" "$PROOF_EXTRA_FLAGS" \
    "$PROOF_OBJECT_BITS" "$TIMEOUT" "${result_base}/sat_cadical"

  # Run 3: SAT with MiniSat
  echo "  [3/${n_runs}] Running with MiniSat SAT backend..."
  run_cbmc_backend "$goto_file" "--sat-solver minisat2" "$PROOF_EXTRA_FLAGS" \
    "$PROOF_OBJECT_BITS" "$TIMEOUT" "${result_base}/sat_minisat"

  # Runs 4-5: If the proof uses --no-array-field-sensitivity, re-run SMT and
  # SAT (CaDiCaL) without it to compare the effect of field sensitivity.
  if $has_nafs; then
    local extra_with_afs
    extra_with_afs="$(echo "$PROOF_EXTRA_FLAGS" | sed 's/--no-array-field-sensitivity//')"

    echo "  [4/${n_runs}] Running SMT with array field sensitivity..."
    run_cbmc_backend "$goto_file" "$original_backend_args" "$extra_with_afs" \
      "$PROOF_OBJECT_BITS" "$TIMEOUT" "${result_base}/smt_afs"

    echo "  [5/${n_runs}] Running CaDiCaL SAT with array field sensitivity..."
    run_cbmc_backend "$goto_file" "--sat-solver cadical" "$extra_with_afs" \
      "$PROOF_OBJECT_BITS" "$TIMEOUT" "${result_base}/sat_cadical_afs"
  fi

  # Print summary for this proof
  print_meta() {
    local label="$1" meta="$2"
    local result="N/A" wall_time_s="N/A" max_rss_kb="N/A"
    if [[ -f "$meta" ]]; then
      eval "$(grep -E '^(result|wall_time_s|max_rss_kb)=' "$meta")"
    fi
    printf "  %-16s result=%-22s time=%s  mem=%s KB\n" \
      "$label" "$result" "$wall_time_s" "$max_rss_kb"
  }
  print_meta "SMT:" "${result_base}/smt.meta"
  print_meta "CaDiCaL:" "${result_base}/sat_cadical.meta"
  print_meta "MiniSat:" "${result_base}/sat_minisat.meta"
  if $has_nafs; then
    print_meta "SMT+AFS:" "${result_base}/smt_afs.meta"
    print_meta "CaDiCaL+AFS:" "${result_base}/sat_cadical_afs.meta"
  fi
}

########################################################################
# Generate summary report
########################################################################

generate_report() {
  local report_file="${RESULTS_DIR}/summary.csv"
  echo "repo,proof,backend,result,exit_code,wall_time_s,max_rss_kb" > "$report_file"

  for repo_dir in "${RESULTS_DIR}"/*/; do
    local repo_name
    repo_name="$(basename "$repo_dir")"
    for proof_dir in "${repo_dir}"/*/; do
      [[ -d "$proof_dir" ]] || continue
      local proof_name
      proof_name="$(basename "$proof_dir")"

      # Skip if build failed
      if [[ -f "${proof_dir}/build.meta" ]]; then
        local build_result
        build_result="$(grep '^build_result=' "${proof_dir}/build.meta" | cut -d= -f2)"
        if [[ "${build_result}" != "OK" ]]; then
          echo "${repo_name},${proof_name},build,${build_result},,,," >> "$report_file"
          continue
        fi
      fi

      for backend in smt sat_cadical sat_minisat smt_afs sat_cadical_afs; do
        local meta="${proof_dir}/${backend}.meta"
        [[ -f "$meta" ]] || continue
        local result exit_code wall_time_s max_rss_kb
        eval "$(grep -E '^(result|exit_code|wall_time_s|max_rss_kb)=' "$meta")"
        echo "${repo_name},${proof_name},${backend},${result},${exit_code},${wall_time_s},${max_rss_kb}" >> "$report_file"
      done
    done
  done

  echo ""
  echo "=== Summary Report ==="
  echo "Full CSV: $report_file"
  echo ""

  # Print per-proof results in a compact vertical format
  for repo_dir in "${RESULTS_DIR}"/*/; do
    local repo_name
    repo_name="$(basename "$repo_dir")"
    for proof_dir in "${repo_dir}"/*/; do
      [[ -d "$proof_dir" ]] || continue
      local proof_name
      proof_name="$(basename "$proof_dir")"

      printf "%-20s %-40s" "$repo_name" "$proof_name"
      for backend in smt sat_cadical sat_minisat smt_afs sat_cadical_afs; do
        local meta="${proof_dir}/${backend}.meta"
        [[ -f "$meta" ]] || continue
        local result="N/A" wall_time_s="N/A" max_rss_kb="N/A"
        eval "$(grep -E '^(result|wall_time_s|max_rss_kb)=' "$meta")"
        local label
        case $backend in
          smt)              label="smt";;
          sat_cadical)      label="cadical";;
          sat_minisat)      label="minisat";;
          smt_afs)          label="smt+afs";;
          sat_cadical_afs)  label="cad+afs";;
        esac
        printf "  %s=%-8s/%ss/%sMB" "$label" "$result" "$wall_time_s" \
          "$(echo "$max_rss_kb" | awk '{ if ($1+0 > 0) printf "%.0f", $1/1024; else print "N/A" }')"
      done
      echo ""
    done
  done

  # Print aggregate stats
  echo ""
  echo "=== Aggregate ==="
  for backend in smt sat_cadical sat_minisat smt_afs sat_cadical_afs; do
    local label
    case $backend in
      smt)              label="SMT (original)";;
      sat_cadical)      label="SAT (CaDiCaL)";;
      sat_minisat)      label="SAT (MiniSat)";;
      smt_afs)          label="SMT (+AFS)";;
      sat_cadical_afs)  label="SAT CaDiCaL (+AFS)";;
    esac
    local total=0 success=0 failure=0 timeout=0 error=0 invariant=0 oom=0 other=0
    while IFS=, read -r _repo _proof _be res _ec _wt _mem; do
      [[ "$_be" == "$backend" ]] || continue
      ((total++)) || true
      case "$res" in
        SUCCESS)              ((success++)) || true;;
        FAILURE)              ((failure++)) || true;;
        TIMEOUT)              ((timeout++)) || true;;
        ERROR)                ((error++)) || true;;
        INVARIANT_VIOLATION)  ((invariant++)) || true;;
        OOM)                  ((oom++)) || true;;
        *)                    ((other++)) || true;;
      esac
    done < <(tail -n+2 "$report_file")
    printf "  %-20s total=%-4d success=%-4d failure=%-4d timeout=%-4d oom=%-4d error=%-4d invariant=%-4d other=%-4d\n" \
      "$label" "$total" "$success" "$failure" "$timeout" "$oom" "$error" "$invariant" "$other"
  done

  # Highlight mismatches: proofs where any non-SMT backend gives a different result
  echo ""
  echo "=== Mismatches (non-SMT result differs from SMT baseline) ==="
  local found_mismatch=false
  for repo_dir in "${RESULTS_DIR}"/*/; do
    local repo_name
    repo_name="$(basename "$repo_dir")"
    for proof_dir in "${repo_dir}"/*/; do
      [[ -d "$proof_dir" ]] || continue
      local proof_name
      proof_name="$(basename "$proof_dir")"

      local smt_r=""
      [[ -f "${proof_dir}/smt.meta" ]] && smt_r="$(grep '^result=' "${proof_dir}/smt.meta" | cut -d= -f2)"
      [[ "$smt_r" == "SKIPPED" ]] && continue

      local mismatch_line=""
      for backend in sat_cadical sat_minisat smt_afs sat_cadical_afs; do
        local meta="${proof_dir}/${backend}.meta"
        [[ -f "$meta" ]] || continue
        local r
        r="$(grep '^result=' "$meta" | cut -d= -f2)"
        if [[ -n "$r" ]] && [[ "$r" != "$smt_r" ]]; then
          mismatch_line="${mismatch_line} ${backend}=${r}"
        fi
      done
      if [[ -n "$mismatch_line" ]]; then
        echo "  ${repo_name}/${proof_name}: SMT=${smt_r}${mismatch_line}"
        found_mismatch=true
      fi
    done
  done
  $found_mismatch || echo "  (none)"
}

########################################################################
# Main
########################################################################

# Set memory limit: default to 85% of total system RAM
if [[ -z "$MEMLIMIT_KB" ]]; then
  total_kb=$(awk '/^MemTotal:/ { print $2 }' /proc/meminfo)
  MEMLIMIT_KB=$(( total_kb * 85 / 100 ))
fi
echo "=== Configuration ==="
echo "CBMC:       $CBMC"
echo "Work dir:   $WORK_DIR"
echo "Results:    $RESULTS_DIR"
echo "Timeout:    ${TIMEOUT}s per proof"
echo "Mem limit:  $(( MEMLIMIT_KB / 1024 )) MB"
echo "Parallel:   $PARALLEL"
echo "Repos:      $REPOS"
echo ""

run_repo() {
  local repo_name="$1" repo_url="$2" param_var="$3" param_val="$4"
  local repo_dir="${WORK_DIR}/${repo_name}"

  [[ -d "$repo_dir" ]] || return 0

  echo ""
  echo "========================================"
  echo "  Processing: $repo_name"
  echo "========================================"

  local proofs
  mapfile -t proofs < <(list_proofs "$repo_dir")
  echo "Found ${#proofs[@]} proofs"

  local running=0
  local pids=()
  for proof in "${proofs[@]}"; do
    # Apply filter if specified
    if [[ -n "$PROOF_PATTERN" ]] && ! echo "$proof" | grep -qE "$PROOF_PATTERN"; then
      continue
    fi

    if [[ "$PARALLEL" -le 1 ]]; then
      process_proof "$repo_name" "$repo_dir" "$proof" "$param_var" "$param_val"
    else
      # Wait if we've hit the parallel limit
      while [[ ${#pids[@]} -ge $PARALLEL ]]; do
        local new_pids=()
        for pid in "${pids[@]}"; do
          if kill -0 "$pid" 2>/dev/null; then
            new_pids+=("$pid")
          else
            wait "$pid" 2>/dev/null || true
          fi
        done
        pids=("${new_pids[@]}")
        if [[ ${#pids[@]} -ge $PARALLEL ]]; then
          sleep 1
        fi
      done

      # Launch in background, redirecting output to a log file
      local log_file="${RESULTS_DIR}/${repo_name}/${proof}/parallel.log"
      mkdir -p "$(dirname "$log_file")"
      (
        process_proof "$repo_name" "$repo_dir" "$proof" "$param_var" "$param_val"
      ) > "$log_file" 2>&1 &
      pids+=($!)
      echo "  Launched: $proof (pid $!, ${#pids[@]}/$PARALLEL slots)"
    fi
  done

  # Wait for remaining background jobs
  if [[ "$PARALLEL" -gt 1 ]] && [[ ${#pids[@]} -gt 0 ]]; then
    echo "  Waiting for ${#pids[@]} remaining jobs..."
    for pid in "${pids[@]}"; do
      wait "$pid" 2>/dev/null || true
    done
  fi
}

if [[ "$REPOS" == *mlkem* ]]; then
  run_repo mlkem-native \
    https://github.com/pq-code-package/mlkem-native.git \
    MLKEM_K 3
fi

if [[ "$REPOS" == *mldsa* ]]; then
  run_repo mldsa-native \
    https://github.com/pq-code-package/mldsa-native.git \
    MLD_CONFIG_PARAMETER_SET 65
fi

generate_report

echo ""
echo "Done. Results in: $RESULTS_DIR"
