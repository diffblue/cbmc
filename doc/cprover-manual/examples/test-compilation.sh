#!/bin/bash
# Verify that all example files compile against the CProver API.
#
# The CProver API (org.cprover.CProver) is provided by cprover-api.jar from
# https://github.com/diffblue/java-cprover-api. In the CBMC tree it is built by
# the java-models-library submodule into
# jbmc/lib/java-models-library/target/cprover-api.jar, e.g. with:
#   (cd jbmc/lib/java-models-library && mvn dependency:copy@copy-dependencies)
#
# Usage: test-compilation.sh [path-to-cprover-api.jar]
# The jar may also be given via the CPROVER_API_JAR environment variable;
# otherwise the in-tree build location is used.

set -e

orig_pwd="$(pwd)"
script_dir="$(cd "$(dirname "$0")" && pwd)"

cprover_api_jar="${1:-${CPROVER_API_JAR:-$script_dir/../../../jbmc/lib/java-models-library/target/cprover-api.jar}}"
# Resolve a relative path against the original working directory.
case "$cprover_api_jar" in
  /*) ;;
  *) cprover_api_jar="$orig_pwd/$cprover_api_jar" ;;
esac

if [ ! -f "$cprover_api_jar" ]; then
  echo "error: cprover-api.jar not found at: $cprover_api_jar" >&2
  echo "Build it from the java-models-library submodule:" >&2
  echo "  (cd jbmc/lib/java-models-library && mvn dependency:copy@copy-dependencies)" >&2
  echo "or obtain it from https://github.com/diffblue/java-cprover-api" >&2
  exit 1
fi

cd "$script_dir"

echo "Compiling Java modeling examples against:"
echo "  $cprover_api_jar"

# Compile into a throwaway directory so no .class files are left in the tree.
out_dir="$(mktemp -d)"
trap 'rm -rf "$out_dir"' EXIT
javac -cp "$cprover_api_jar" -d "$out_dir" *.java

echo "All examples compiled successfully"
echo ""
echo "Note: these examples are meant to be analyzed with JBMC, not executed"
echo "with a regular JVM. To verify, e.g.:"
echo "  jbmc BankingExample --function BankingExample.verifyTransfer"
