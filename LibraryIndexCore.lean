import Lean

/-! # Library-index extractor core

Shared by the Causalean `library_index` exe and the CausalSmith `paper_index`
exe: walks an elaborated environment and produces `DeclEntry` records (statement,
source, docstring, refs, axioms) for every non-auxiliary declaration under a
module prefix. -/

open Lean

/-- External (non-Causalean) constant referenced by a statement: name + defining
module, so the site can deep-link into the official Mathlib docs. -/
structure ExtRef where
  n : String
  m : String
  deriving ToJson

structure DeclEntry where
  name : String
  kind : String
  module : String
  file : String
  line : Nat
  statement : String
  /-- Verbatim source of the declaration: for a `def` the construction after `:=`
  IS the definition; for theorems the slice includes the proof, rendered behind
  an expandable link. Capped at `sourceSliceCap` lines. -/
  source : Option String
  doc : Option String
  refs : Array String
  proofRefs : Array String
  /-- Mathlib/core constants in the statement, for external doc links. -/
  extRefs : Array ExtRef
  axioms : Array String
  usesSorry : Bool
  deriving ToJson

def auxSuffixes : List String :=
  ["mk", "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "ndrec",
   "noConfusion", "noConfusionType", "injEq", "sizeOf_spec", "toCtorIdx",
   "ofNat", "ctorIdx", "ctorElim", "ctorElimType", "ofNat_ctorIdx"]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Column width for pretty-printing statements into the library index. Kept
generous because the site renders statements in a horizontally-scrollable block:
a wide budget keeps logical lines intact instead of collapsing deeply-nested
statements to one or two symbols per line. -/
def stmtPPWidth : Nat := 1000

def moduleToFile (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

def nameComponentStrings : Name → List String
  | .anonymous => []
  | .str p s => nameComponentStrings p ++ [s]
  | .num p n => nameComponentStrings p ++ [toString n]

def declarationLeaf (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

def isAuxiliary (n : Name) : Bool :=
  n.isInternalDetail ||
  n.hasMacroScopes ||
  (nameComponentStrings n |>.any (fun s => s.startsWith "_" || auxSuffixes.contains s)) ||
  match n with
  | .str _ s =>
      auxSuffixes.contains s || s.startsWith "proof_" || s.startsWith "match_"
  | _ => true

def isLibModule (pfx : Name) (m : Name) : Bool :=
  pfx.isPrefixOf m

def moduleNameOf? (env : Environment) (n : Name) : Option Name := do
  let midx ← env.getModuleIdxFor? n
  env.header.moduleNames[midx.toNat]?

def isLibDecl (pfx : Name) (env : Environment) (n : Name) : Bool :=
  match moduleNameOf? env n with
  | some m => isLibModule pfx m
  | none => false

def shouldSkipDecl (env : Environment) (n : Name) : Bool :=
  isAuxiliary n ||
  env.isConstructor n ||
  env.isProjectionFn n ||
  -- compiler-generated companions namespaced under a constructor (e.g. `BBDir.fromChild.elim`)
  env.isConstructor n.getPrefix

def uniqueSortedStrings (xs : Array String) : Array String :=
  xs.foldl
      (fun acc x =>
        if acc.contains x then acc else acc.push x)
      #[] |>.qsort (· < ·)

def directUsedConstants (ci : ConstantInfo) : Array Name :=
  let bodyConsts :=
    match ci.value? (allowOpaque := true) with
    | some value => value.getUsedConstants
    | none => #[]
  let inductCtors :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ bodyConsts ++ inductCtors

/-- Non-Causalean statement constants with their defining modules (Mathlib, Std,
Lean core …), deduplicated, skipping auxiliaries and instances. -/
def extRefsFor (pfx : Name) (env : Environment) (type : Expr) : Array ExtRef :=
  let seen := type.getUsedConstants.foldl (init := (#[], ({} : NameSet))) fun (acc, s) c =>
    if s.contains c || isAuxiliary c then (acc, s)
    else match moduleNameOf? env c with
      | some m =>
        if isLibModule pfx m then (acc, s.insert c)
        else ((acc.push { n := c.toString, m := m.toString }), s.insert c)
      | none => (acc, s.insert c)
  seen.1

def refsFor (pfx : Name) (env : Environment) (self : Name) (type : Expr) : Array String :=
  type.getUsedConstants.filterMap (fun n =>
    if n == self || shouldSkipDecl env n then
      none
    else
      match moduleNameOf? env n with
      | some m =>
          if isLibModule pfx m then
            some n.toString
          else
            none
      | none => none)
  |> uniqueSortedStrings

def proofRefsFor (pfx : Name) (env : Environment) (self : Name) (stmtRefs : Array String)
    (val? : Option Expr) : Array String :=
  match val? with
  | none => #[]
  | some v =>
      Id.run do
        let mut out := #[]
        for n in v.getUsedConstantsAsSet do
          if n != self && !shouldSkipDecl env n then
            match moduleNameOf? env n with
            | some m =>
                let r := n.toString
                if isLibModule pfx m && !stmtRefs.contains r then
                  out := out.push r
            | none => pure ()
        return uniqueSortedStrings out

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM (Option String) := do
  match ci with
  | .inductInfo _ =>
      if isClass env n then
        return some "class"
      else if isStructure env n then
        return some "structure"
      else
        return some "inductive"
  | .defnInfo _ =>
      if ← Meta.isInstance n then
        return some "instance"
      else
        return some "def"
  | .thmInfo _ =>
      -- Prop-valued instances compile to theorems; classify them as instances too.
      if ← Meta.isInstance n then
        return some "instance"
      else
        return some "theorem"
  | .axiomInfo _ => return some "axiom"
  | .opaqueInfo _ => return some "opaque"
  | .ctorInfo _ => return none
  | .recInfo _ => return none
  | .quotInfo _ => return none

def lineOfDecl (n : Name) : CoreM Nat := do
  match ← findDeclarationRanges? n with
  | some ranges => return ranges.range.pos.line
  | none => return 0

/-- Source-line cache per module file (read once, sliced per declaration). -/
abbrev FileCache := IO.Ref (NameMap (Array String))

def sourceSliceCap : Nat := 150

/-- When Lean does not persist a declaration docstring (notably for a named
`local instance`), recover an immediately preceding `/-- ... -/` block from
the source so the published index retains its natural-language explanation. -/
partial def precedingDocStart? (lines : Array String) (lo : Nat) : Option Nat :=
  let rec seekOpen (i fuel : Nat) : Option Nat :=
    if i == 0 || fuel == 0 then none
    else
      let j := i - 1
      if (lines[j]!.trimAscii.toString).startsWith "/--" then some j
      else seekOpen j (fuel - 1)
  -- Declaration ranges omit doc-comments and may retain an old source offset
  -- after a comment-only edit; the nearest doc block within this short preamble
  -- window is therefore the declaration's own documentation.
  seekOpen lo 16

def leadingDocString? (source : String) : Option String :=
  match source.splitOn "/--" with
  | _ :: rest =>
      match rest.head?.bind (fun after => (after.splitOn "-/").head?) with
      | some doc =>
          let doc := doc.trimAscii.toString
          if doc.isEmpty then none else some doc
      | none => none
  | [] => none

/-- Verbatim source slice of a declaration, from its declaration range; leading
doc-comment lines are kept (the site strips them for display). Truncated at
`sourceSliceCap` lines. -/
def sourceFor (cache : FileCache) (modName : Name) (srcRoot file : String) (n : Name) :
    CoreM (Option String) := do
  let some ranges ← findDeclarationRanges? n | return none
  let lines ← do
    if let some ls := (← cache.get).find? modName then
      pure ls
    else
      let ls ← (do
        let content ← IO.FS.readFile (srcRoot ++ "/" ++ file)
        pure (content.splitOn "\n").toArray) <|> pure #[]
      cache.modify (·.insert modName ls)
      pure ls
  if lines.isEmpty then return none
  let declLo := ranges.range.pos.line - 1      -- 1-indexed → 0-indexed
  let sourceDeclLo? := lines.findIdx? fun line =>
    let line := line.trimAscii.toString
    (line.startsWith "local " || line.startsWith "private ") && line.contains (declarationLeaf n)
  -- An attached doc-comment is part of Lean's declaration range, so in the
  -- usual case `declLo` already points at the opening `/--`.  Searching
  -- backwards unconditionally would then steal the preceding declaration's
  -- docstring whenever the two declarations are close together.
  let rangeStartsWithDoc :=
    (lines[declLo]?.map (fun line =>
      (line.trimAscii.toString).startsWith "/--")).getD false
  let docLo? :=
    if rangeStartsWithDoc then some declLo
    else
      precedingDocStart? lines declLo <|>
        sourceDeclLo?.bind (precedingDocStart? lines)
  let lo := docLo?.getD declLo
  let hi := min ranges.range.endPos.line lines.size
  if lo ≥ hi then return none
  let slice := (Array.range (hi - lo)).map (fun i => lines[lo + i]!)
  let slice := if slice.size > sourceSliceCap then
      (slice.take sourceSliceCap).push "  -- … truncated; follow the source link for the rest …"
    else slice
  return some ("\n".intercalate slice.toList)

partial def axiomStringsFor (pfx : Name)
    (cache : IO.Ref (NameMap (Array String))) (seen : NameMap Unit) (n : Name) :
    CoreM (Array String) := do
  if let some cached := (← cache.get).find? n then
    return cached
  if seen.contains n then
    return #[]
  let env ← getEnv
  let result ←
    match env.find? n with
    | none => pure #[]
    | some (.axiomInfo _) =>
        if standardAxioms.contains n then
          pure #[]
        else
          pure #[n.toString]
    | some ci =>
        if !isLibDecl pfx env n then
          pure #[]
        else
          let mut out := #[]
          for used in directUsedConstants ci do
            out := out ++ (← axiomStringsFor pfx cache (seen.insert n ()) used)
          pure <| uniqueSortedStrings out
  cache.set ((← cache.get).insert n result)
  return result

def entryFor? (pfx : Name) (srcRoot : String)
    (axiomCache : IO.Ref (NameMap (Array String))) (fileCache : FileCache)
    (ci : ConstantInfo) : CoreM (Option DeclEntry) := do
  let env ← getEnv
  let n := ci.name
  if !isLibDecl pfx env n || shouldSkipDecl env n then
    return none
  let some moduleName := moduleNameOf? env n
    | return none
  let some kind ← kindOf env n ci
    | return none
  -- A def nested under another def/instance is a compiler- or where-generated
  -- worker (`instRepr*.repr`, `instDecidableEq*.decEq`, `f.go`), not a library
  -- declaration. Theorems namespaced under a def are kept.
  if kind == "def" || kind == "instance" then
    if let some (.defnInfo _) := env.find? n.getPrefix then
      return none
  let fmt ← Meta.MetaM.run' <|
    withOptions
      (fun opts =>
        opts
          |>.setBool `pp.deepTerms true
          |>.set `pp.maxSteps (200000 : Nat))
      (Meta.ppExpr ci.type)
  -- Pretty-print at a generous width: the site shows statements in a
  -- horizontally-scrollable block, so we want the pretty-printer to keep each
  -- logical line intact rather than break deeply-nested statements down to one
  -- or two symbols per line (indentation alone exhausts a narrow width).
  let statement := fmt.pretty (width := stmtPPWidth)
  let statement ←
    if statement.contains '⋯' then
      let fmt ← Meta.MetaM.run' <|
        withOptions
          (fun opts =>
            opts
              |>.setBool `pp.deepTerms true
              |>.set `pp.maxSteps (200000 : Nat)
              |>.set `pp.proofs.threshold (200000 : Nat))
          (Meta.ppExpr ci.type)
      pure (fmt.pretty (width := stmtPPWidth))
    else
      pure statement
  let envDoc ← liftM <| findDocString? env n
  let axioms ← axiomStringsFor pfx axiomCache {} n
  let refs := refsFor pfx env n ci.type
  let proofRefs := proofRefsFor pfx env n refs ci.value?
  let file := moduleToFile moduleName
  -- Theorems carry their source too: the proof renders behind an expandable
  -- "Proof" link on the site (statement stays the primary view).
  let source ← sourceFor fileCache moduleName srcRoot file n
  -- Prefer an authored source doc block when present: Lean can retain an empty
  -- environment doc entry for named local instances, which must not mask the
  -- source fallback used by the public index.
  let doc := (source.bind leadingDocString?).orElse fun _ => envDoc
  return some {
    name := n.toString
    kind := kind
    module := moduleName.toString
    file := file
    line := ← lineOfDecl n
    statement := statement
    source := source
    doc := doc
    refs := refs
    proofRefs := proofRefs
    extRefs := extRefsFor pfx env ci.type
    axioms := axioms
    usesSorry := axioms.contains "sorryAx"
  }

def buildEntries (pfx : Name) (srcRoot : String) : CoreM (Array DeclEntry) := do
  let env ← getEnv
  let axiomCache ← liftM <| IO.mkRef ({} : NameMap (Array String))
  let fileCache : FileCache ← liftM <| IO.mkRef ({} : NameMap (Array String))
  let mut entries := #[]
  for (_, ci) in env.constants.toList do
    match ← entryFor? pfx srcRoot axiomCache fileCache ci with
    | some entry => entries := entries.push entry
    | none => pure ()
  return entries.qsort (fun a b => a.name < b.name)

def gitCommit : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  if out.exitCode == 0 then
    return out.stdout.trimAscii.toString
  else
    throw <| IO.userError s!"git rev-parse HEAD failed: {out.stderr.trimAscii.toString}"

def gitCommitIn (dir : String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"], cwd := dir }
  if out.exitCode == 0 then
    return out.stdout.trimAscii.toString
  else
    throw <| IO.userError s!"git rev-parse HEAD failed: {out.stderr.trimAscii.toString}"

/-- Shared driver: import `importRoot`, index every declaration under `pfx`, and
write the JSON index (entries + per-module docs) to `outPath`. -/
-- `extraModules` are imported alongside `importRoot`. For per-paper indexing
-- the paper's own modules are passed here so the index does NOT depend on the
-- paper being wired into `importRoot`'s import graph — an accepted paper that
-- was never added to the package root would otherwise index to 0 declarations
-- (silent empty Formalization page).
unsafe def runIndex (importRoot pfx : Name) (srcRoot outPath : String)
    (extraModules : Array Name := #[]) : IO Unit := do
  initSearchPath (← findSysroot)
  -- Load persistent env extensions (instance attribute, module docs) — without
  -- this every instance classifies as a plain def/theorem.
  enableInitializersExecution
  -- When the paper's own modules are given, import THOSE only — not the package
  -- root, whose import graph may pull in other (possibly unbuilt) papers'
  -- modules and abort the load. The paper modules transitively bring their deps.
  let roots := if extraModules.isEmpty then #[importRoot] else extraModules
  let imports := roots.map (fun m => { module := m : Import })
  let env ← importModules imports {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<library_index>", fileMap := default }
  let cstate : Core.State := { env }
  let (entries, _) ← (buildEntries pfx srcRoot).toIO ctx cstate
  let moduleDocs : List (String × Json) :=
    env.header.moduleNames.toList.filterMap fun m =>
      if isLibModule pfx m then
        let doc := (Lean.getModuleDoc? env m).bind (·[0]?) |>.map (·.doc.trimAscii.toString)
        some (m.toString, match doc with | some s => Json.str s | none => Json.null)
      else none
  let json := Json.mkObj [
    ("commit", toJson (← gitCommitIn ".")),
    ("toolchain", toJson "leanprover/lean4:v4.29.0-rc3"),
    ("modules", Json.mkObj moduleDocs),
    ("entries", toJson entries)
  ]
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath (json.pretty ++ "\n")
  IO.println s!"library_index: {entries.size} declarations -> {outPath}"
