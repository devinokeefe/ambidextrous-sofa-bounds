#!/usr/bin/env bash
# Tests of check_cert.py: exit status, strict reading of the certificate, and the log of finished tasks.
# Run from the data folder:  bash ../checkers/test_check_cert.sh
# Uses small certificates only; takes a few minutes. Set PY to choose the Python interpreter.
PY=${PY:-$(command -v python3 || command -v python)}
DRV="$(dirname "$0")/check_cert.py"
TMP=$(mktemp -d)
if [ -z "$CHECK_ARITH" ]; then   # FLINT if installed, otherwise Python's fractions
  if "$PY" -c "import flint" 2>/dev/null; then CHECK_ARITH=flint; else CHECK_ARITH=fraction; fi
fi
export CHECK_ARITH
echo "python: $PY ; arithmetic: $CHECK_ARITH"
fails=0
expect() {  # expect CODE PATTERN -- command...
  local code=$1 pat=$2; shift 3
  out=$("$@" 2>&1); got=$?
  last=$(printf '%s\n' "$out" | tail -1)
  if [ "$got" = "$code" ] && printf '%s' "$out" | grep -q "$pat"; then
    echo "PASS  exit $got  $last"
  else
    echo "FAIL  exit $got (wanted $code, /$pat/)  $last"; fails=$((fails + 1))
  fi
}
mkspec() {  # mkspec SRC T CERT OUT
  "$PY" -c "import json,sys; s=json.load(open(sys.argv[1])); s['T']=sys.argv[2]; s['cert']=sys.argv[3]; json.dump(s,open(sys.argv[4],'w'))" "$1" "$2" "$3" "$4"
}

echo "== 1. one-leaf certificate: Gamma(E0) = 5, checked against T = 5 and T = 353/200"
echo "L" > "$TMP/one.txt"
mkspec specs/c_3653_1765.json 5 "$TMP/one.txt" "$TMP/one_T5.json"
mkspec specs/c_3653_1765.json 353/200 "$TMP/one.txt" "$TMP/one_T1765.json"
expect 0 "CERTIFICATE VALID"   -- "$PY" -B "$DRV" "$TMP/one_T5.json" 2 "$TMP/one.log"
expect 2 "LOG REFUSED"         -- "$PY" -B "$DRV" "$TMP/one_T1765.json" 2 "$TMP/one.log"
expect 1 "CERTIFICATE INVALID" -- "$PY" -B "$DRV" "$TMP/one_T1765.json" 2 "$TMP/one_fresh.log"

echo "== 2. certificate for T = 2 (c_3653_20), split into many tasks"
expect 0 "CERTIFICATE VALID"   -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20.log" 500
n=$(($(wc -l < "$TMP/c20.log") - 1)); echo "   $n task records"
head -n $((n / 2 + 1)) "$TMP/c20.log" > "$TMP/c20_half.log"
expect 0 "already done $((n / 2))" -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_half.log" 500
echo "== 3. tampered logs are refused"
awk 'NR==2{$4=$4+1} {print}' "$TMP/c20.log" > "$TMP/c20_count.log"
expect 2 "does not match task" -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_count.log" 500
awk 'NR==2{$6="0000000000000000"} {print}' "$TMP/c20.log" > "$TMP/c20_box.log"
expect 2 "does not match task" -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_box.log" 500
{ cat "$TMP/c20.log"; sed -n 2p "$TMP/c20.log"; } > "$TMP/c20_dup.log"
expect 2 "duplicate"           -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_dup.log" 500
expect 2 "LOG REFUSED"         -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20.log" 400

echo "== 4. same certificate against T = 19/10: rejected, also when reusing the T = 2 log"
mkspec specs/c_3653_20.json 19/10 certs/cert_c_3653_20.txt "$TMP/c20_T19.json"
expect 1 "CERTIFICATE INVALID" -- "$PY" -B "$DRV" "$TMP/c20_T19.json" 4 "$TMP/c20_T19.log" 500
expect 2 "LOG REFUSED"         -- "$PY" -B "$DRV" "$TMP/c20_T19.json" 4 "$TMP/c20.log" 500

echo "== 5. truncated certificate"
head -c 400000 certs/cert_c_3653_20.txt > "$TMP/trunc.txt"
mkspec specs/c_3653_20.json 2 "$TMP/trunc.txt" "$TMP/trunc.json"
expect 1 "CERTIFICATE INVALID" -- "$PY" -B "$DRV" "$TMP/trunc.json" 2 "$TMP/trunc.log"

echo "== 6. malformed input: usage errors and unusable logs exit with 2, a malformed certificate with 1"
awk 'NR==2{$1="x"} {print}' "$TMP/c20.log" > "$TMP/c20_idx.log"
expect 2 "malformed record"    -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_idx.log" 500
awk 'NR==2{$4="many"} {print}' "$TMP/c20.log" > "$TMP/c20_cnt.log"
expect 2 "malformed record"    -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_cnt.log" 500
awk 'NR==2{$2="1/0"} {print}' "$TMP/c20.log" > "$TMP/c20_val.log"
expect 2 "malformed record"    -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_val.log" 500
awk 'NR==2{$3=-1} {print}' "$TMP/c20.log" > "$TMP/c20_neg.log"
expect 2 "malformed record"    -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/c20_neg.log" 500
expect 2 "positive integer"    -- "$PY" -B "$DRV" specs/c_3653_20.json four "$TMP/u1.log"
expect 2 "positive integer"    -- "$PY" -B "$DRV" specs/c_3653_20.json 0 "$TMP/u2.log"
expect 2 "positive integer"    -- "$PY" -B "$DRV" specs/c_3653_20.json 4 "$TMP/u3.log" 0
expect 2 "cannot read spec"    -- "$PY" -B "$DRV" "$TMP/no_such_spec.json" 4 "$TMP/u4.log"
mkspec specs/c_3653_20.json 2 "$TMP/no_such_cert.txt" "$TMP/nocert.json"
expect 2 "cannot read spec"    -- "$PY" -B "$DRV" "$TMP/nocert.json" 4 "$TMP/u5.log"
mkspec specs/c_3653_20.json abc certs/cert_c_3653_20.txt "$TMP/badT.json"
expect 2 "cannot read spec"    -- "$PY" -B "$DRV" "$TMP/badT.json" 4 "$TMP/u6.log"
printf '0 L X\n' > "$TMP/badchar.txt"
mkspec specs/c_3653_20.json 2 "$TMP/badchar.txt" "$TMP/badchar.json"
expect 1 "CERTIFICATE INVALID" -- "$PY" -B "$DRV" "$TMP/badchar.json" 2 "$TMP/u7.log"

echo "== 7. certificate tokens outside the grammar; unreadable or unwritable files"
echo "255" > "$TMP/t255.txt"
mkspec specs/c_3653_20.json 5 "$TMP/t255.txt" "$TMP/t255.json"
expect 1 "not a valid token"   -- "$PY" -B "$DRV" "$TMP/t255.json" 2 "$TMP/v1.log"
echo "8 L L" > "$TMP/t8.txt"
mkspec specs/c_3653_20.json 5 "$TMP/t8.txt" "$TMP/t8.json"
expect 1 "not below 8"         -- "$PY" -B "$DRV" "$TMP/t8.json" 2 "$TMP/v2.log"
echo "+0 L L" > "$TMP/tplus.txt"
mkspec specs/c_3653_20.json 5 "$TMP/tplus.txt" "$TMP/tplus.json"
expect 1 "character other than" -- "$PY" -B "$DRV" "$TMP/tplus.json" 2 "$TMP/v3.log"
mkdir "$TMP/logdir"
expect 2 "cannot read"         -- "$PY" -B "$DRV" specs/c_3653_20.json 2 "$TMP/logdir" 500
printf '\377\376\n' > "$TMP/badutf.log"
expect 2 "cannot read"         -- "$PY" -B "$DRV" specs/c_3653_20.json 2 "$TMP/badutf.log" 500
expect 2 "cannot create log"   -- "$PY" -B "$DRV" specs/c_3653_20.json 2 "$TMP/no_such_dir/x.log" 500
cp certs/cert_c_3653_20.txt "$TMP/noread.txt"; chmod 000 "$TMP/noread.txt"
mkspec specs/c_3653_20.json 2 "$TMP/noread.txt" "$TMP/noread.json"
if [ -r "$TMP/noread.txt" ]; then
  echo "SKIP  unreadable certificate: permissions cannot make a file unreadable here (root, or Windows)"
else
  expect 2 "cannot read certificate" -- "$PY" -B "$DRV" "$TMP/noread.json" 2 "$TMP/v4.log"
fi
chmod 644 "$TMP/noread.txt"

echo "== 8. a write failure during the run (file-size limit of 1 KiB): no verdict, exit 2"
case "$(uname -s)" in
  Linux|Darwin)
    # shellcheck disable=SC2016  # $0 and $@ are expanded by the inner bash
    expect 2 "no verdict" -- bash -c 'ulimit -f 1; exec "$0" "$@"' "$PY" -B "$DRV" specs/c_3653_20.json 2 "$TMP/wf.log" 500 ;;
  *) echo "SKIP  write failure: needs ulimit -f (Linux or macOS)" ;;
esac

rm -rf "$TMP"
echo "failures: $fails"
exit $fails
