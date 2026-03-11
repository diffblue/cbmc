"""Utility functions for the profiling tool."""

import shutil
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent

RED = '\033[0;31m'
GREEN = '\033[0;32m'
YELLOW = '\033[0;33m'
BLUE = '\033[0;34m'
NC = '\033[0m'


def die(msg):
    print(f"{RED}[ERROR]{NC} {msg}", file=sys.stderr)
    sys.exit(1)


def info(msg):
    print(f"{BLUE}[INFO]{NC} {msg}")


def ok(msg):
    print(f"{GREEN}[OK]{NC} {msg}")


def warn(msg):
    print(f"{YELLOW}[WARN]{NC} {msg}")


def check_prerequisites():
    """Verify all required tools are installed."""
    info("Checking prerequisites...")

    if not shutil.which("perf"):
        die("perf not found. Install linux-tools-$(uname -r)")

    try:
        paranoid = int(Path("/proc/sys/kernel/perf_event_paranoid").read_text().strip())
    except (FileNotFoundError, ValueError):
        die("Cannot read /proc/sys/kernel/perf_event_paranoid")
    if paranoid > -1:
        die(f"perf_event_paranoid={paranoid} (need -1). "
            "Fix with: sudo sysctl kernel.perf_event_paranoid=-1")

    if not shutil.which("cmake"):
        die("cmake not found")

    ok(f"perf available, perf_event_paranoid={paranoid}")


def ensure_cbmc(build_dir):
    """Check that CBMC binary exists."""
    cbmc = build_dir / "bin" / "cbmc"
    if not cbmc.is_file():
        die(f"CBMC binary not found at {cbmc}. Build first with: "
            f"cmake --build {build_dir} --target cbmc")
    ok(f"CBMC binary: {cbmc}")
    return cbmc


def ensure_flamegraph(flamegraph_dir):
    """Ensure FlameGraph scripts are available."""
    if flamegraph_dir and (Path(flamegraph_dir) / "flamegraph.pl").is_file():
        return Path(flamegraph_dir)

    fg_dir = REPO_ROOT / ".flamegraph"
    if not (fg_dir / "flamegraph.pl").is_file():
        info("Cloning FlameGraph repository...")
        subprocess.run(
            ["git", "clone", "--depth", "1",
             "https://github.com/brendangregg/FlameGraph.git", str(fg_dir)],
            capture_output=True, check=True)
        # Pin to a known good commit for reproducibility
        subprocess.run(
            ["git", "checkout", "v1.0"],
            cwd=str(fg_dir), capture_output=True)
    ok(f"FlameGraph tools: {fg_dir}")
    return fg_dir
