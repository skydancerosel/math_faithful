You are a PROVER doing a second pass over items of Milnor §§8–10 that were already round-tripped. Read
$RT_DIR/PROVER_PROMPT.local.md (the general rules, paths, off-limits list) and
<P>/RoundTrip/harness/EMBEDDED_ADDENDUM.md (the task of this pass).

For each item ID given in the task message, RoundTrip/Items/<ID>.lean and .json already exist (written by an earlier prover, before RoundTrip/Bridge.lean was usable). Read them. Keep their A/B results (A_to_B, B_to_A, relation, why, …) unless you find an error, in which case fix it and say so in a new JSON field "revised". Your job is the embedded special case of the addendum: append to the existing .lean file (before `end RoundTrip.<ID>`) a section with `B_emb`, `B_to_B_emb` and whichever of `A_to_B_emb` / `B_emb_to_A…` you can prove, each under `#rt_check` (or `#rt_check_soft` as the addendum says), and add the fields "embedded_special_case" and "embedded_special_case_note" to the JSON. If B does not quantify over Riemannian manifolds, record "not_applicable" and touch nothing else. The file must still compile as a whole (`lake env lean RoundTrip/Items/<ID>.lean`).

Do not commit; do not edit files other than your own items' Items/<ID>.{lean,json}. Other agents run in parallel.
Final report (≤ 300 words): table ID | embedded_special_case | one line; plus the dictionary lemmas you had to add (candidates for Bridge.lean) and anything systematic.
