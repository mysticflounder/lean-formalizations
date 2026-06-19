# Automation cost/time raw log-mining results (working file — not final)

Source data for formalization.yaml `automation` field. Mined 2026-06-18 from
Claude Code, Codex, and OpenCode session logs across erdos-98, esgk-on3,
lean-formalizations. **Codex pending** (background agent still running).

## Claude Code (`~/.claude/projects/<enc>/*.jsonl`)

| Project | Sessions | Calendar span | Active hrs (15min cap) | Models | Output tok | Cache-read tok |
|---|---|---|---|---|---|---|
| lean-formalizations | 8 | 2026-05-29 → 06-19 (20.3 d) | 51.2 | opus-4-8 only | 36.80M | 1.452B |
| esgk-on3 | 1 | 2026-05-28 → 06-18 (21.0 d) | 28.1 | opus-4-8, sonnet-4-6 | 8.47M | 471M |
| erdos-98 | 15 | 2026-05-16 → 06-18 (32.9 d) | 88.5 | fable-5, opus-4-6/4-7/4-8, sonnet-4-6 | 36.52M | 3.440B |

lean-formalizations Claude totals (opus-4-8): input 4,027,178 · output 36,798,633 · cache_creation 109,216,133 · cache_read 1,452,401,341.
erdos-98 Claude: opus-4-7 dominant (18,911 msgs, 25.3M out), then opus-4-8 (5,367 msgs, 8.78M out), fable-5 (798 msgs), opus-4-6, sonnet-4-6.

## OpenCode (`~/.local/share/opencode/opencode.db` — SQLite `session` table, has REAL USD cost)

| Project | Sessions | Span | Active hrs | Cost USD | Models | input/output/reasoning tok |
|---|---|---|---|---|---|---|
| lean-formalizations | 10 | 2026-06-16 → 06-18 | 18.78 | $13.27 | deepseek-v4-pro (7) + local MLX (3, $0) | 1.92M / 0.49M / 0.63M |
| erdos-98 | 4 | 2026-06-03 → 06-18 | 7.18 | $8.65 | deepseek-v4-pro | 7.96M / 0.20M / 0.06M |
| esgk-on3 | 0 | — | — | — | — | not used in OpenCode |

OpenCode cost column = real recorded USD. lean cache_read 454.7M; erdos-98 cache_read 24.6M.
FLAG: a separate dir `/Users/adam/projects/math-projects/erdos-97-96` (1 OpenCode session, $12.05, 1.18M input) exists — NOT rolled into erdos-98 (exact-path attribution). Confirm whether erdos-97-96 should be reported separately or merged.

## Codex (`~/.codex/sessions/2026/**/*.jsonl`, attribution by session_meta/turn_context cwd; tokens = Σ last_token_usage deltas, reset-immune)

| Project | Sessions | Calendar span | Active hrs (Σ per-session, concurrent) | Output tok | Input tok (cached) | Total tok | Plan |
|---|---|---|---|---|---|---|---|
| lean-formalizations | 19 | 2026-06-04 → 06-15 (10.4 d) | 141.8 | 15.60M | 2.608B (2.482B cached) | 2.632B | pro |
| esgk-on3 | 2 (still active 06-19) | 06-18 → 06-19 (0.9 d) | 37.2 | 2.33M | 663M (643M cached) | 667M | pro |
| erdos-98 | 103 | 2026-05-18 → 06-19 (31.8 d) | 336.2 | 43.60M | 8.994B (8.593B cached) | 9.068B | plus→pro |

Clean cwd partition (no file in >1 project). Codex Pro = flat subscription. Model name not extracted (recoverable from turn_context if needed).

## SYNTHESIS — lean-formalizations (formalization.yaml target)

- **Models**: Claude opus-4-8 (Claude Code); OpenAI/Codex models (Codex CLI, Pro); deepseek-v4-pro + local MLX (Qwen3.6/gemma-4/DeepSeek-Prover-V2) via OpenCode.
- **Wall time (calendar union)**: 2026-05-29 → 06-19 ≈ **21 days (~3 weeks)**.
- **Aggregate agent active-time** (parallel/overlapping, NOT human hours): Claude 51.2h + Codex 141.8h + OpenCode 18.8h ≈ **212 agent-hours** (Codex figure inflated by concurrent worktree panes).
- **Spend, two honest framings**:
  - *Actual out-of-pocket*: **$13.27** metered (OpenCode/DeepSeek) + Claude Max subscription + Codex Pro subscription (both flat-rate).
  - *Notional API-equivalent (Claude opus-4-8 portion)*: ≈ **$7,050** = out 36.80M×$75 ($2,760) + cache-wr 109.2M×$18.75 ($2,048) + cache-rd 1.452B×$1.50 ($2,179) + in 4.03M×$15 ($60). Codex portion not priced (subscription; model/rate unconfirmed).

## Cross-project totals (Adam asked about all three)

| Project | Claude active-h / out-tok | Codex active-h / out-tok | OpenCode $ | Calendar span |
|---|---|---|---|---|
| lean-formalizations | 51.2h / 36.8M | 141.8h / 15.6M | $13.27 | 05-29→06-19 (~3wk) |
| erdos-98 | 88.5h / 36.5M | 336.2h / 43.6M | $8.65 | 05-16→06-19 (~4.7wk) |
| esgk-on3 | 28.1h / 8.47M | 37.2h / 2.33M | $0 (unused) | 05-28→06-19 (~3wk) |

FLAGS: (1) `erdos-97-96` is a SEPARATE OpenCode dir ($12.05, 1 session) — not merged into erdos-98. (2) esgk-on3 + erdos-98 Codex sessions were still active on 06-19 (open snapshots). (3) Fable-5 appears only in erdos-98 Claude logs, not lean. (4) erdos-98 Codex plan upgraded plus→pro mid-span.

## Notional pricing (Anthropic list, per MTok) for $ estimate — Claude is subscription so this is API-equivalent, not out-of-pocket
- Opus tier (4.6/4.7/4.8): $15 in / $75 out / $18.75 cache-write / $1.50 cache-read
- Sonnet 4.6: $3 / $15 / $3.75 / $0.30
- Fable 5: list price not confirmed — {{NEEDS_ADAM_INPUT}}

lean-formalizations Claude notional ≈ $60(in) + $2,760(out) + $2,048(cache-wr) + $2,179(cache-rd) ≈ **$7,047** (API-equivalent; actual = Max subscription).
