#!/bin/sh
# TypeTheory's test suite on the v2 kernel and on Wolfram 15, side by side, on the build pods:
#     sh benchmarks/kernels/v2/lane.sh [<kernel commit>]
# The tree is this checkout's HEAD (git archive) with what a release paclet adds, all of which must be there: the
# environments saved at HEAD (TypeTheory/Environments), the Linux library (TypeTheory/LibraryResources/Linux-x86-64)
# and KernelCompiler (TT_KERNELCOMPILER, the installed Wolfram__KernelCompiler-0.1.1), as KernelCompiler/ at its root.
# It goes to ~/TypeTheory-lanes/<commit> on a lanes pod and on the Wolfram 15 pod.
# The v2 column: the kernel commit (main of the kernel repository by default) built in a lane (pod-lane.sh, pod dir
# TypeTheory-v2), each test file in a kernel of its own, 600 s and 6 GB each, four at a time
# (scripts/run_tests_by_file.sh under the kernel tree's memcap.py). The Wolfram 15 column: the whole suite in one
# Wolfram 15 kernel on the w15 pod (`w15`). Both run benchmarks/kernels/v2/with_kernelcompiler.wls.
# Output: $TT_OUT (default ./v2-run), with lane.out, w15.out, and the v2 column's per-file logs in test-runs/.
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
pods=${KERNEL_PODS:-$HOME/src/wolfram/kernel-pods}; kernel=${KERNEL_REPO:-$HOME/src/wolfram/kernel}
out=${TT_OUT:-./v2-run}; mkdir -p "$out" || exit 2; out=$(cd "$out" && pwd)
compiler=${TT_KERNELCOMPILER:-$HOME/Library/Wolfram/Paclets/Repository/Wolfram__KernelCompiler-0.1.1}
sha=$(git -C "$root" rev-parse --verify HEAD) || exit 2; short=$(echo "$sha" | cut -c1-12)
ksha=$(git -C "$kernel" rev-parse --verify "${1:-main}^{commit}") || { echo "lane.sh: no kernel commit ${1:-main}"; exit 2; }
for need in "$root/TypeTheory/Environments/Machine.wxf" "$root/TypeTheory/LibraryResources/Linux-x86-64/TypeTheoryKernel-Wolfram-15.0.so" "$compiler/PacletInfo.wl"; do
	[ -f "$need" ] || { echo "lane.sh: $need is missing"; exit 2; }
done
P() { POD_HOST=$1 sh "$pods/pod.sh" "$2"; }
Pi() { POD_HOST=$1 sh "$pods/pod.sh" -i "$2"; }
# the tree: the commit, then the release's additions, then the compiler
stage=$(mktemp -d "${TMPDIR:-/tmp}/tt-v2.XXXXXX") || exit 2
trap 'rm -rf "$stage" "$stage.tgz" "$stage.send"' EXIT
git -C "$root" archive --format=tar "$sha" | tar -xf - -C "$stage" || exit 2
mkdir -p "$stage/TypeTheory/Environments" "$stage/TypeTheory/LibraryResources/Linux-x86-64" "$stage/KernelCompiler"
cp "$root"/TypeTheory/Environments/*.wxf "$stage/TypeTheory/Environments/" && cp "$root"/TypeTheory/LibraryResources/Linux-x86-64/* "$stage/TypeTheory/LibraryResources/Linux-x86-64/" &&
	cp -R "$compiler"/. "$stage/KernelCompiler/" || exit 2
COPYFILE_DISABLE=1 tar --no-mac-metadata -czf "$stage.tgz" -C "$stage" . || exit 2
echo "lane.sh: TypeTheory $short ($(wc -c < "$stage.tgz" | tr -d ' ') bytes), kernel $(echo "$ksha" | cut -c1-12)"
# the pod command's own status, its output without tar's warnings about macOS metadata
send() {
	Pi "$1" "rm -rf ~/TypeTheory-lanes/$short && mkdir -p ~/TypeTheory-lanes/$short && tar -xzf - -C ~/TypeTheory-lanes/$short" < "$stage.tgz" > "$stage.send" 2>&1; status=$?
	grep -v LIBARCHIVE "$stage.send"; echo "lane.sh: TypeTheory $short on $1, status $status"; return $status
}
# the lanes pod with the most free slots now
freest() { best=; most=-1; for p in $(sh "$pods/pod-addr.sh" --role lanes); do f=0; for l in $(sh "$pods/pod-addr.sh" --slots "$p" | awk '{ print $1 }'); do lockf -s -t 0 "$l" true 2> /dev/null && f=$((f + 1)); done; [ "$f" -gt "$most" ] && { most=$f; best=$p; }; done; echo "$best"; }
pod=${TT_POD:-$(freest)}; w15=$(sh "$pods/pod-addr.sh" --role w15 | head -1)
send "$pod" || exit 1
send "$w15" || exit 1
# the Wolfram 15 column, beside the lane
(
	P "$w15" "cd ~/TypeTheory-lanes/$short && s=\$(date +%s); W15_WAIT=7200 W15_MEM=8g W15_TIMEOUT=10800 w15 benchmarks/kernels/v2/with_kernelcompiler.wls > run-w15.log 2>&1; st=\$?; grep -a -E '^  (ok|FAIL)  |failed: |^(PASS|FAIL)  ' run-w15.log; echo \"lane.sh: Wolfram 15 exit \$st in \$((\$(date +%s) - s)) s\""
) > "$out/w15.out" 2>&1 &
w15pid=$!
# the v2 column
rm -f "$out/w15.full.log"
POD_HOST=$pod POD_LANE_OWNER=TypeTheory POD_LANE_TIMEOUT=${TT_TIMEOUT:-14400} sh "$pods/pod-lane.sh" "$ksha" TypeTheory-v2 \
	"cd \$HOME/TypeTheory-lanes/$short && mkdir -p .bin && ln -sfn \"\$WL\" .bin/wolframscript && PATH=\$PWD/.bin:\$PATH && s=\$(date +%s); TT_MEMCAP=\$HOME/TypeTheory-v2/KernelCompiler/Scripts/memcap.py TT_RUNNER=benchmarks/kernels/v2/with_kernelcompiler.wls TT_CPUS=\$CPUS sh scripts/run_tests_by_file.sh 600 4; echo \"lane.sh: v2 column in \$((\$(date +%s) - s)) s\"" 2>&1 | tee "$out/lane.out"
# the per-file logs and Wolfram 15's whole log
P "$pod" "cd ~/TypeTheory-lanes/$short && tar -czf - .test-runs" > "$out/test-runs.tgz" 2> /dev/null && mkdir -p "$out/test-runs" && tar -xzf "$out/test-runs.tgz" -C "$out/test-runs" --strip-components 1
wait "$w15pid"
P "$w15" "cat ~/TypeTheory-lanes/$short/run-w15.log" > "$out/w15.full.log" 2> /dev/null
echo "== Wolfram 15"; tail -3 "$out/w15.out"
echo "== results in $out"
