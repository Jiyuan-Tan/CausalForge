import LibraryIndexCore

/-! # Paper-module index exe

Indexes the Lean modules of a paper run (`--prefix CausalSmith.Stat.X_Research`)
into a bundle's `paper_library_index.json`, for the site's per-paper
Formalization view. Defaults to the whole CausalSmith package. -/

unsafe def main (args : List String) : IO Unit := do
  let get (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let pfx := (get "--prefix").map (·.toName) |>.getD `CausalSmith
  let some out := get "--out"
    | throw <| IO.userError "usage: paper_index --out <path> [--prefix <module-prefix>] [--modules m1,m2,…]"
  let srcRoot := (get "--src-root").getD "CausalSmith"
  -- The paper's own modules, imported directly so the index does not rely on the
  -- paper being reachable from the `CausalSmith` root (orphaned-paper → 0 decls).
  let extra : Array Lean.Name :=
    ((get "--modules").getD "").splitOn ","
      |>.filterMap (fun s =>
          let t := s.trimAscii.toString
          if t.isEmpty then none else some t.toName)
      |>.toArray
  runIndex `CausalSmith pfx srcRoot out extra
