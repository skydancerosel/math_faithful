import Morse
open Lean Meta Elab Command

/-- Dump every non-theorem, non-instance, non-auxiliary declaration of the project's modules. -/
elab "#dump_vocab" : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Morse).isPrefixOf mod || (`Milnor).isPrefixOf mod do continue
    if n.isInternal || isAuxRecursor env n || isNoConfusion env n then continue
    if (← liftCoreM (Lean.Meta.isInstance n)) then continue
    if n.toString.endsWith "_def" || n.toString.endsWith ".eq_1" then continue
    let kind ← match ci with
      | .defnInfo _ => pure "def" | .inductInfo _ => pure "inductive"
      | .opaqueInfo _ => pure "opaque" | _ => pure ""
    if kind == "" then continue
    let (isP, ty) ← liftTermElabM <| do
        let b ← isProp ci.type
        let f ← ppExpr ci.type
        pure (b, toString f)
    if !isP then
      let doc := (← findDocString? env n).getD ""
      out := out.push s!"### {mod} · {kind} {n}\n{ty}\n{doc.trimAscii}\n"
  let dir := (← IO.getEnv "RT_DIR").getD "/tmp/claude-0/rt"
  IO.FS.writeFile (dir ++ "/vocab.md") (String.intercalate "\n" (out.qsort (· < ·)).toList)
#dump_vocab
