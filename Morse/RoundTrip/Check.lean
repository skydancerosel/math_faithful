import Lean
/-!
# Round-trip harness: "no peeking" check

`#rt_check T [n₁, …, nₖ]` fails unless the proof of `T` avoids the declarations `nᵢ`, directly
and through every project lemma it uses. The traversal follows constants from the project's own
modules (`Morse.*`, `Milnor.*`, `RoundTrip.*`) and stops at Mathlib, which cannot depend on them.
-/
open Lean Elab Command

/-- The body of a declaration, theorems included. -/
def rtValue? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def rtCollect (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  let mut todo := todo
  let mut seen := seen
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Morse).isPrefixOf m || (`Milnor).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let deps := ci.type.getUsedConstants ++ ((rtValue? ci).map (·.getUsedConstants)).getD #[]
      todo := deps.toList ++ todo
  return seen

elab "#rt_check " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some _ := env.find? t.getId | throwError "unknown {t.getId}"
  let ci := (env.find? t.getId).get!
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList {}
  if used.contains ``sorryAx then throwError "rt_check FAIL: {t.getId} contains sorry (or failed to elaborate)"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  if bad.isEmpty then logInfo m!"rt_check OK: {t.getId} avoids the banned declarations"
  else throwError "rt_check FAIL: {t.getId} uses {bad}"

/-- `#rt_overlap T [n₁, …, nₖ]` lists the project theorems that the proof of `T` shares with the
proofs of the `nᵢ`: lemmas of the formal proof that a round-trip proof reuses. Not an error;
reviewed by hand. -/
elab "#rt_overlap " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList {}
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      ((`Morse).isPrefixOf n || (`Milnor).isPrefixOf n)
  logInfo m!"rt_overlap {t.getId}: {shared.length} shared project theorems {shared}"

/-- The project definitions that the *statement* of `n` rests on: the constants of its type,
then of the types and bodies of the project definitions among them, down to Mathlib. -/
partial def rtDefClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  let mut todo := todo
  let mut seen := seen
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => false
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Morse).isPrefixOf m || (`Milnor).isPrefixOf m
      unless inProject do continue
      seen := seen.insert n
      let body := match ci with
        | .defnInfo v => v.value.getUsedConstants
        | .inductInfo v => v.ctors.toArray
        | .ctorInfo v => v.type.getUsedConstants
        | _ => #[]
      todo := (ci.type.getUsedConstants ++ body).toList ++ todo
  return seen

/-- `#rt_defs [t₁, …]` prints the project definitions under the statements of the `tᵢ`. -/
elab "#rt_defs " " [" ts:ident,* "]" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for t in ts.getElems do
    let some ci := env.find? t.getId | throwError "unknown {t.getId}"
    roots := (roots.push t.getId) ++ ci.type.getUsedConstants
  let cl := rtDefClosure env roots.toList {}
  let defs := cl.toList.filter fun n => match env.find? n with
    | some (.thmInfo _) => false | some _ => !n.isInternal | none => false
  let lines := defs.map fun n =>
    let m := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString | none => "?"
    s!"{m} {n}"
  let dir := (← IO.getEnv "RT_DIR").getD "/tmp/claude-0/rt"
  IO.FS.writeFile (dir ++ "/defs.txt") (String.intercalate "\n" (lines.toArray.qsort (· < ·)).toList)
  logInfo m!"{defs.length} project definitions"

/-- `D._proof_N`: a proof that Lean abstracted out of the body of the definition `D`. -/
def rtIsDefProof (n : Name) : Bool := match n with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

/-- Like `rtCollect`, but separating the constants reached only through the abstracted proof
fields (`D._proof_N`) of project *definitions* (`soft`) from those reached otherwise (`hard`). -/
partial def rtCollectSoft (env : Environment) (todo : List (Name × Bool)) (hard soft : NameSet) :
    NameSet × NameSet := Id.run do
  let mut todo := todo
  let mut hard := hard
  let mut soft := soft
  while true do
    match todo with
    | [] => break
    | (n, isHard) :: rest =>
      todo := rest
      if hard.contains n then continue
      if !isHard && soft.contains n then continue
      if isHard then hard := hard.insert n else soft := soft.insert n
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Morse).isPrefixOf m || (`Milnor).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let isDef := match ci with | .defnInfo _ => true | _ => false
      let tys := ci.type.getUsedConstants.toList.map (·, isHard)
      let vals := (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList.map fun c =>
        (c, isHard && !(isDef && rtIsDefProof c))
      todo := tys ++ vals ++ todo
  return (hard, soft)

/-- `#rt_check_soft T [n₁, …, nₖ]`: as `#rt_check`, except that a banned `nᵢ` reached only through
the proof fields of a project definition (e.g. a bilinear map whose `map_add'` is proved with `nᵢ`,
or a metric space whose axioms are) does not fail the check but is listed for review. Use it only
when `#rt_check` fails for that reason, and say in the JSON which definitions were involved. -/
elab "#rt_check_soft " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let (hard, soft) := rtCollectSoft env (roots.toList.map (·, true)) {} {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "rt_check_soft FAIL: {t.getId} contains sorry (or failed to elaborate)"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  let badSoft := banned.filter fun b => soft.contains b && !hard.contains b
  unless badHard.isEmpty do throwError "rt_check_soft FAIL: {t.getId} uses {badHard}"
  if badSoft.isEmpty then logInfo m!"rt_check_soft OK: {t.getId} avoids the banned declarations"
  else
    let defs := (hard.toList.filter fun n => match env.find? n with
      | some (.defnInfo v) => v.value.getUsedConstants.any fun c =>
          rtIsDefProof c && (let cl := rtCollect env [c] {}; badSoft.any cl.contains)
      | _ => false)
    logInfo m!"rt_check_soft OK with review: {t.getId} reaches {badSoft} only through the proof fields of definitions among {defs}"
