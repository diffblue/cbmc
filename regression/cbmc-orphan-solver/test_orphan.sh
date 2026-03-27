#!/bin/sh
# Test that solver child processes are terminated when CBMC is killed.
# Linux-specific (relies on PR_SET_PDEATHSIG).

CBMC=../../src/cbmc/cbmc
[ -x "$CBMC" ] || CBMC=../../build/bin/cbmc
[ -x "$CBMC" ] || { echo "FAILED: cannot find cbmc"; exit 1; }

PIDFILE=/tmp/cbmc_test_solver_$$.pid
rm -f "$PIDFILE"
trap "rm -f $PIDFILE fake_solver_tmp_$$.sh" EXIT

# Create a solver script with our unique PID file
cat > fake_solver_tmp_$$.sh <<EOF
#!/bin/sh
trap '' PIPE
echo \$\$ > $PIDFILE
while read line; do :; done
sleep 60
EOF
chmod +x fake_solver_tmp_$$.sh

# Launch CBMC
$CBMC main.c \
  --incremental-smt2-solver ./fake_solver_tmp_$$.sh \
  >/dev/null 2>&1 &
CBMC_PID=$!

# Wait for solver to write its PID
for i in 1 2 3 4 5; do
  [ -s "$PIDFILE" ] && break
  sleep 1
done

if [ ! -s "$PIDFILE" ]; then
  echo "FAILED: solver did not start"
  kill $CBMC_PID 2>/dev/null
  exit 1
fi

SOLVER_PID=$(cat "$PIDFILE")

# Kill CBMC with SIGKILL (cannot clean up)
kill -9 $CBMC_PID 2>/dev/null
wait $CBMC_PID 2>/dev/null

# Give kernel time to deliver PDEATHSIG
sleep 2

if kill -0 "$SOLVER_PID" 2>/dev/null; then
  echo "FAILED: solver is still running (orphan)"
  kill "$SOLVER_PID" 2>/dev/null
  exit 1
fi

echo "PASSED"
