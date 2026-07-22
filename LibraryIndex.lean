import LibraryIndexCore

/-! # Causalean library-index exe

Walks the elaborated environment of `import Causalean` and writes
`doc/library_index.json` for the site's `/library` explorer. -/

unsafe def main : IO Unit :=
  runIndex `Causalean `Causalean "." "doc/library_index.json"
