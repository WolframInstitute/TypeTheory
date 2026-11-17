#!/bin/sh
# Runs each test file in a kernel of its own, with a time limit, several at a time:
#     sh scripts/run_tests_by_file.sh [<seconds> [<jobs>]] [<file.wlt> ...]
# <seconds> (600) limits each file and <jobs> (4) run side by side. The files are the arguments, or every .wlt under
# TypeTheory/Tests. A line for each file as it ends: scripts/run_tests.wls's own "ok" or "FAIL" line with the file's
# seconds, TIMEOUT or MEMORY where it was stopped, or NORESULT where it ended without its line. Then a summary line,
# and exit status 0 only when every file passed. Each file's whole output is in .test-runs/<file>.log.
# The kernel is $WL when it is set, else wolframscript; TT_RUNNER is the script it runs with the file
# (scripts/run_tests.wls, or a wrapper that loads a paclet first and then gets it). TT_MEMCAP, the path of a memcap.py
# (the Wolfram kernel repository's KernelCompiler/Scripts/memcap.py), runs each kernel under it, capped at
# TT_MEMORY_GB (6) of its process tree's footprint as well as the time limit; a file killed at the cap is MEMORY.
# TT_CPUS, a processor list, runs each kernel on those processors (taskset), where taskset is there.
cd "$(dirname "$0")/.." || exit 2
limit=600; jobs=4
case "${1:-}" in [0-9]*) limit=$1; shift ;; esac
case "${1:-}" in [0-9]*) jobs=$1; shift ;; esac
dir=.test-runs; rm -rf "$dir"; mkdir -p "$dir"; : > "$dir/results"
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else find TypeTheory/Tests -name '*.wlt' | sort; fi > "$dir/files"
kernel=${WL:-wolframscript}; runner=${TT_RUNNER:-scripts/run_tests.wls}; memcap=${TT_MEMCAP:-}; memory=${TT_MEMORY_GB:-6}
pin=; [ -n "${TT_CPUS:-}" ] && command -v taskset > /dev/null && pin="taskset -c $TT_CPUS"
export limit dir kernel runner memcap memory pin
xargs -P "$jobs" -n 1 sh -c '
	f=$1; log="$dir/$(echo "$f" | tr / _).log"; start=$(date +%s)
	killed=
	if [ -n "$memcap" ]; then
		$pin python3 "$memcap" --cap-gb "$memory" --timeout "$limit" --report "$log.json" -- "$kernel" -f "$runner" "$f" < /dev/null > "$log" 2>&1; status=$?
		killed=$(python3 -c "import json, sys; print(json.load(open(sys.argv[1])).get(\"killed\") or \"\")" "$log.json" 2> /dev/null)
	else
		$pin timeout -k 30 "$limit" "$kernel" -f "$runner" "$f" < /dev/null > "$log" 2>&1; status=$?
		{ [ "$status" = 124 ] || [ "$status" = 137 ]; } && killed=time
	fi
	took=$(( $(date +%s) - start ))
	case "$killed" in
		memory) line="  MEMORY  $f  past $memory GB after $took s" ;;
		time | timeout) line="  TIMEOUT  $f  after $took s" ;;
		*) line="$(grep -a -E "^  (ok|FAIL)  " "$log" | head -1)"; line="${line:-  NORESULT  $f  exit $status}  $took s" ;;
	esac
	echo "$line"; echo "$line" >> "$dir/results"' sh < "$dir/files"
ok=$(grep -c "^  ok " "$dir/results"); fail=$(grep -c "^  FAIL " "$dir/results")
timeouts=$(grep -c "^  TIMEOUT " "$dir/results"); memkills=$(grep -c "^  MEMORY " "$dir/results")
other=$(grep -c "^  NORESULT " "$dir/results")
bad=$((fail + timeouts + memkills + other))
echo
echo "$( [ "$bad" = 0 ] && echo PASS || echo FAIL )  $ok ok, $fail failing, $timeouts timed out, $memkills past the memory cap, $other with no result, of $(wc -l < "$dir/files" | tr -d ' ') files"
[ "$bad" = 0 ]
