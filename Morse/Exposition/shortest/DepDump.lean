import Morse
/-!
The declaration dependency graph of this project and of the Milnor project, for
`Exposition/shortest/deps.py`. Run from `Morse/`:

    lake env lean -DmaxSynthPendingDepth=3 Exposition/shortest/DepDump.lean

It writes `Exposition/shortest/deps.jsonl`: one line per declaration of a `Morse.*` or `Milnor.*`
module, with its module, kind, line, and the project declarations its type (`t`) and its body or
proof (`v`) use directly. Mathlib declarations are leaves: Mathlib cannot depend on the project.
-/
open Lean Elab Command

def dvalue? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def dkind : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

elab "#dep_dump " s:str : command => do
  let env ← getEnv
  let isProj : Name → Option Name := fun n => match env.getModuleIdxFor? n with
    | none => none
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      if (`Morse).isPrefixOf m || (`Milnor).isPrefixOf m then some m else none
  let mut lines : Array String := #[]
  let mut cnt := 0
  for (n, ci) in env.constants.map₁.toList do
    let some m := isProj n | continue
    cnt := cnt + 1
    let tdeps := ci.type.getUsedConstants.filter (fun d => (isProj d).isSome)
    let vdeps := (((dvalue? ci).map (·.getUsedConstants)).getD #[]).filter (fun d => (isProj d).isSome)
    let extra : Array Name := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let rng ← liftCoreM (findDeclarationRanges? n)
    let line : Json := match rng with | some r => toJson r.range.pos.line | none => Json.null
    let j := Json.mkObj [("n", toJson n.toString), ("m", toJson m.toString), ("k", toJson (dkind ci)),
      ("i", toJson n.isInternal), ("l", line),
      ("t", toJson (tdeps.map (·.toString))), ("v", toJson ((vdeps ++ extra).map (·.toString)))]
    lines := lines.push j.compress
  IO.FS.writeFile s.getString (String.intercalate "\n" lines.toList)
  logInfo m!"{cnt} project constants written"

#dep_dump "Exposition/shortest/deps.jsonl"
