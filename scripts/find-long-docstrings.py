#!/usr/bin/env python3
"""Find comment/docstring lines longer than 100 Unicode characters in Lean files.

Tracks nested Lean block comments (/- ... -/, including /-- and /-! variants) and
line comments (--). A line is "comment context" if it begins inside a block comment,
opens one, or is a pure line comment. Emits only such lines whose codepoint length
(NOT byte length) exceeds the limit, so multi-byte unicode (×, ≤, ∩, —, …) does not
inflate the count. Code lines are never emitted.

Usage: find-long-docstrings.py [LIMIT] -- file1.lean file2.lean ...
   or: find-long-docstrings.py [LIMIT]   (reads file list from stdin, one per line)
"""
import sys

def split_args(argv):
    limit = 100
    files = []
    rest = argv[1:]
    if rest and rest[0].isdigit():
        limit = int(rest[0]); rest = rest[1:]
    if rest and rest[0] == "--":
        rest = rest[1:]
    if rest:
        files = rest
    else:
        files = [ln.strip() for ln in sys.stdin if ln.strip()]
    return limit, files

def scan(path, limit):
    depth = 0  # block-comment nesting depth at start of current scan position
    hits = []
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.readlines()
    except (OSError, UnicodeDecodeError) as e:
        print(f"# skip {path}: {e}", file=sys.stderr)
        return hits
    for lineno, raw in enumerate(lines, 1):
        line = raw.rstrip("\n")
        start_depth = depth
        # Walk the line to update block-comment depth and detect line comments.
        i = 0
        in_comment_here = start_depth > 0
        line_comment = False
        n = len(line)
        while i < n:
            two = line[i:i+2]
            if depth > 0:
                if two == "-/":
                    depth -= 1; i += 2; continue
                if two == "/-":
                    depth += 1; i += 2; continue
                i += 1; continue
            else:
                if two == "/-":
                    depth += 1; in_comment_here = True; i += 2; continue
                if two == "--":
                    line_comment = True; in_comment_here = True; break
                i += 1; continue
        is_comment = in_comment_here or line_comment or start_depth > 0
        if is_comment and len(line) > limit:
            kind = "block" if (start_depth > 0 or depth > 0 or "/-" in line) else "line"
            hits.append((lineno, len(line), kind, line[:70]))
    return hits

def main():
    limit, files = split_args(sys.argv)
    total = 0
    per_file = {}
    for path in files:
        hits = scan(path, limit)
        if hits:
            per_file[path] = hits
            total += len(hits)
    for path in sorted(per_file):
        for (ln, length, kind, snip) in per_file[path]:
            print(f"{path}:{ln} ({length}c, {kind}) {snip}")
    print(f"# TOTAL: {total} comment/docstring lines > {limit} chars across {len(per_file)} files", file=sys.stderr)

if __name__ == "__main__":
    main()
