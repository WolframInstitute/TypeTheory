#!/bin/sh
# Fetches the converter the documentation is built with: MarkdownToNotebook.wl at the commit pacletpage.wl names, into
# deps/MarkdownToNotebook/, checked against the SHA-256 pacletpage.wl names. It comes from a checkout of
# MarkdownToNotebook that has the commit (MARKDOWNTONOTEBOOK_DIR, by default the one next to this checkout), and
# otherwise from GitHub.
#     sh scripts/fetch_converter.sh
repo=$(cd "$(dirname "$0")/.." && pwd)
commit=$(sed -n 's/^\$converterCommit = "\([0-9a-f]\{40\}\)"$/\1/p' "$repo/pacletpage.wl")
sha256=$(sed -n 's/^\$converterSHA256 = "\([0-9a-f]\{64\}\)"$/\1/p' "$repo/pacletpage.wl")
if [ -z "$commit" ] || [ -z "$sha256" ]; then
	echo "fetch_converter: pacletpage.wl names no converter commit and hash"
	exit 1
fi
checkout=${MARKDOWNTONOTEBOOK_DIR:-$repo/../MarkdownToNotebook}
target=$repo/deps/MarkdownToNotebook/MarkdownToNotebook.wl
partial=$target.partial
mkdir -p "$(dirname "$target")" || exit 1
if git -C "$checkout" cat-file -e "$commit:MarkdownToNotebook.wl" 2>/dev/null; then
	source=$checkout
	git -C "$checkout" show "$commit:MarkdownToNotebook.wl" > "$partial"
else
	source=GitHub
	curl -fsSL "https://raw.githubusercontent.com/WolframInstitute/MarkdownToNotebook/$commit/MarkdownToNotebook.wl" -o "$partial"
fi
if [ $? -ne 0 ]; then
	rm -f "$partial"
	echo "fetch_converter: MarkdownToNotebook $commit could not be read from $source"
	exit 1
fi
actual=$(shasum -a 256 "$partial" | cut -d ' ' -f 1)
if [ "$actual" != "$sha256" ]; then
	rm -f "$partial"
	echo "fetch_converter: the file from $source has SHA-256 $actual, not $sha256"
	exit 1
fi
mv "$partial" "$target"
echo "fetch_converter: MarkdownToNotebook $(echo "$commit" | cut -c 1-7) from $source, in deps/MarkdownToNotebook"
