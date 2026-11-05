You are the PROVER in a round-trip audit of a Lean 4 formalization of Milnor's *Morse Theory* (project /home/user/math_faithful/Morse; `export PATH=$HOME/.elan/bin:$PATH`; check files with `cd /home/user/math_faithful/Morse && lake env lean <file>`; build a module with `lake build RoundTrip.Blind.<ID>`). Do NOT commit. Other Lean agents share the machine (memory is tight): compile ONE file at a time; if an .olean is reported missing because another agent is rebuilding, wait a minute and retry.

Item IDs: listed in /tmp/claude-0/rt/<BATCH>.
For each ID:
- B := `RoundTrip.<ID>.B` in /home/user/math_faithful/Morse/RoundTrip/Blind/<ID>.lean — an independent formalization of Milnor's statement by someone who never saw the project's theorem. Do NOT edit Blind files (if B has a bug that makes it not mean what Milnor says, record it in B_issue).
- A := the project's formal statement: the declarations in /tmp/claude-0/rt/decls/<ID>.txt. Definitions there are vocabulary; A is the conjunction of the TYPES of the listed THEOREMS (`type_of% @Name.{0,…}` — instantiate universes at 0 since B lives in `Type`; record that). If the item lists only definitions, A = True: then instead compare the project's definitions with B's notions (prove they agree, as in RoundTrip/Items/V1_2.lean) and report that.
- Milnor's text: /tmp/claude-0/rt/blind/<ID>.md. Do NOT read /tmp/claude-0/rt/keys/ or Morse/Exposition/cmp/ or Morse/Exposition/Verification.md (they contain the expected answers).
- Worked examples (read 2–3 first): /home/user/math_faithful/Morse/RoundTrip/Items/{V2_13,V1_15,V3_12,V2_9}.lean and .json. Reuse their glue (e.g. the homeomorphism between hand-built cell attachments and `Morse.AttachCell` in V2_13.lean) — if you factor reusable glue, put it in /home/user/math_faithful/Morse/RoundTrip/Glue.lean (create or append; namespace RoundTrip.Glue; build with `lake build RoundTrip.Glue`).

Write /home/user/math_faithful/Morse/RoundTrip/Items/<ID>.lean:
```lean
import Morse
import RoundTrip.Check
import RoundTrip.Blind.<ID>
namespace RoundTrip.<ID>
def A : Prop := …
theorem A_holds : A := …
theorem A_to_B : A → B := …        -- only if fully proved
theorem B_to_A : B → A := …        -- only if fully proved
-- theorem not_B : ¬ B := …        -- only if B is false and you proved it
#rt_check RoundTrip.<ID>.A_to_B [<fully qualified theorem names from decls>]
#rt_check RoundTrip.<ID>.B_to_A [<same>]
#rt_overlap RoundTrip.<ID>.B_to_A [<same>]
end RoundTrip.<ID>
```
Rules: no `sorry`/`admit`/axioms; omit directions you can't prove. Every included direction must pass `#rt_check` (you may NOT use the item's own theorems, directly or through lemmas built on them; in A_to_B use the hypothesis). You MAY use Mathlib and any other project lemma (grep /home/user/math_faithful/Morse/Morse/ freely). Budget roughly 20–30 minutes of effort per item: real effort on glue (unfolding, specializing settings, transporting along homeomorphisms) is expected, but when a direction would need re-proving substantial mathematics, stop and diagnose. The diagnosis is the main output: say precisely what one side has that the other lacks, and whether a failure is a genuine difference or only proof effort.

Also write /home/user/math_faithful/Morse/RoundTrip/Items/<ID>.json:
{"id": "...", "A_to_B": "proved|failed|false", "B_to_A": "proved|failed|false", "not_B": true|false, "relation": "equivalent|A_stronger|A_narrower|incomparable|unclear", "effort_only": true|false, "why": "<2–5 sentences: the precise mathematical difference, or why a proof failed>", "B_issue": null|"...", "overlap": "<summary of #rt_overlap output>", "uses_hypothesis": {"A_to_B": true|false, "B_to_A": true|false}}
(uses_hypothesis: false when a direction was proved by proving its conclusion outright without using the hypothesis — such "equivalences" are vacuous for the audit and must be flagged; when the conclusion is provable outright, still say so, and also say which side has content the other lacks.)
(A_stronger: A ⇒ B only — the formal result proves more than Milnor's claim. A_narrower: B ⇒ A only — the formal result assumes more/covers less. incomparable: each has content the other lacks. effort_only: true if a failed direction is believed TRUE and just not proved.)

Final report (≤ 400 words): table ID | A→B | B→A | relation | one-line why; plus anything systematic.
