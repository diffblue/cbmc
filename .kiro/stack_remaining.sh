#!/bin/bash
# stack_remaining.sh [STACK] [WORK]: what of WORK (the working branch) is not
# yet in STACK (the side branch of to-be-upstreamed PRs), by area.  Paths that
# are not meant for upstream are excluded.  Test descriptions whose only
# difference is the level (CORE/KNOWNBUG) on the first line are counted
# separately: these flip as the code lands.
stack=${1:-upstream-stack}; work=${2:-cpp11-parser-rework-squashed}
excl=(':!.kiro' ':!DOGFOODING.md' ':!CI_KNOWN_FAILURES.md' ':!regression/cbmc-cpp/CONCEPTS_PLAN.md')
level_only=0; other=()
while read -r f; do
  if [[ $f == *.desc ]] && git cat-file -e "$stack:$f" 2>/dev/null &&
     [ "$(git show "$stack:$f" | tail -n +2)" = "$(git show "$work:$f" | tail -n +2)" ]; then
    level_only=$((level_only + 1))
  else
    other+=("$f")
  fi
done < <(git diff --name-only "$stack" "$work" -- . "${excl[@]}")
echo "test descriptions differing only in their level: $level_only"
echo "other files differing: ${#other[@]}"
[ ${#other[@]} -gt 0 ] && git diff --numstat "$stack" "$work" -- "${other[@]}" |
  awk '{split($3,p,"/"); a=p[1]; if(a=="src"||a=="regression"||a=="unit") a=a"/"p[2]; i[a]+=$1; d[a]+=$2; n[a]++}
       END {for(k in n) printf "%8d %8d %5d %s\n", i[k], d[k], n[k], k}' | sort -rn
