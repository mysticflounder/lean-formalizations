
## Proof blueprint

This project is tracked by `proof-blueprint` (`.blueprint.toml` at the repo
root; the Lake root IS the repo root, so `lean_lib = "."`). The DB at
`data/proof-blueprint.db` is a gitignored build artifact — `intent/` is the
durable record. On a fresh clone or worktree, run `proof-blueprint bootstrap`
once. No `[publish] target_symbol` is set (collection repo, no single headline
theorem); no obligations are declared yet — declare them per formalization as
work proceeds. See the math-toolchain `proof-blueprint` skill for usage.

## Memory

This project uses nthdegree for persistent memory.

```bash
nthdegree recall "<query>"              # text output, default
nthdegree recall "<query>" [--format json]   # for scripted ULID extraction
nthdegree store "<content>" --type <decision|feedback|fact|reference>
nthdegree list                           # all memories
nthdegree stats
```

`recall` first before answering questions about past work in this project.
