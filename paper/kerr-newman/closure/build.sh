#!/bin/bash
# Compile the closure modules in dependency order, recording time and peak memory.
CL=$(cd "$(dirname "$0")" && pwd)
export PATH=/root/.elan/bin:$PATH
cd "${WORKSPACE:-/root/prove2me_workspace}"
LP=$(lake env printenv LEAN_PATH)
mkdir -p "$CL/olean/Closure"
while read m; do
  [ -z "$m" ] && continue
  echo "=== $m $(date +%T)"
  LEAN_PATH="$CL/olean:$LP" /usr/bin/time -f "TIME %e s  MAXRSS %M KB" \
    lean --root="$CL/src" -o "$CL/olean/Closure/$m.olean" "$CL/src/Closure/$m.lean" > "$CL/out_$m.txt" 2>&1
  rc=$?
  tail -12 "$CL/out_$m.txt"
  if [ $rc -ne 0 ]; then echo "FAILED $m rc=$rc"; exit 1; fi
done < "$CL/order.txt"
echo CLOSURE_DONE
