/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib
import K3Twists
import Lean.Elab.Command

/-!
Invariant: every Lean name and every `.lean` path cited in a code span of a docstring of the
library (module and declaration docstrings) or of `README.md` exists and is not deprecated.

Run from `src/lean`: `lake env lean scripts/CheckDocNames.lean`. It fails with one line per name
or path that exists nowhere and per deprecated name; with `CHECK_DOC_NAMES_NOTES=1` it also lists
the notes below. It reads the compiled environment, so `K3Twists` must be built. `Mathlib` is
imported whole, so Mathlib's names resolve whether or not the library imports them.

**Names.** A word of a code span is a name if it is an identifier that looks like the name of a
declaration: qualified (`Matrix.PosDef`), two words of two letters or more joined by an underscore
(`classInf_mono`), or camel case (`cycleTime`). Subscripts (`d_T`, `sup_S`), products (`jH`),
fields of variables (`x.r`, `hf.mono`) and schematic names (`Foo.f` for a field `f`) are not. A
name resolves if it is a constant, a namespace, a module, a test module, an option or a keyword, at
the root or under a namespace of a declaration of its module or one its file opens. Failing that,
the end of a constant or namespace (`classInf_mono` of `Profile.classInf_mono`) or generalized
field notation on a constant (`yoneda.obj`) is a note. The README has no namespace, so its names
resolve by suffix without a note. A deprecated name is an error, except in a docstring that says
"deprecated" or next to that word in the README (on its line or the line before or after).

**Paths.** A word ending in `.lean`, with a path split over two code spans or two lines joined and
braces expanded (`Slicing/{PhaseBounds,BoundaryFactors}.lean`), is a path. It resolves relative to
the directory of the citing file or one of its parents, or to Mathlib; failing that, the end of
the path of a file of the library, its tests, these scripts or Mathlib is a note.
-/

open Lean Elab Command

namespace CheckDocNames

/-- The code spans of a Markdown text, with the line (from `0`) each starts on: a run of one or
two backticks up to the next run of the same length. A fenced block, a run of three or more, is
not a span. -/
def codeSpans (s : String) : Array (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut i := 0
  let mut line := 0
  while i < cs.size do
    if cs[i]! != '`' then
      if cs[i]! == '\n' then line := line + 1
      i := i + 1
      continue
    let mut j := i
    while j < cs.size && cs[j]! == '`' do j := j + 1
    let mut k := j
    let mut close : Option (Nat × Nat) := none
    while k < cs.size && close.isNone do
      let mut m := k
      while m < cs.size && cs[m]! == '`' do m := m + 1
      if m > k && m - k == j - i then close := some (k, m) else k := max m (k + 1)
    match close with
    | some (a, b) =>
      let body := (cs.extract j a).toList
      if j - i < 3 then out := out.push (String.ofList body, line)
      line := line + (body.filter (· == '\n')).length
      i := b
    | none => i := j
  return out

/-- The words of a code span that are dotted identifiers, as lists of components. A word with a
`/` is a path, not an identifier. -/
def identWords (s : String) : Array (List String) := Id.run do
  let mut out := #[]
  let mut cur : List Char := []
  for c in s.toList ++ [' '] do
    if isIdRest c || c == '.' || c == '/' then
      cur := c :: cur
      continue
    let segs := ((String.ofList cur.reverse).splitOn ".").filter (· ≠ "")
    cur := []
    if !segs.isEmpty && segs.all fun seg => match seg.toList with
        | c :: cs => isIdFirst c && cs.all isIdRest
        | [] => false then
      out := out.push segs
  return out

/-- Two lowercase letters followed by an uppercase one, as in `classInf`, not `jH`. -/
def isCamel (s : String) : Bool := Id.run do
  let mut run := 0
  for c in s.toList do
    if c.isUpper && run ≥ 2 then return true
    run := if c.isLower then run + 1 else 0
  return false

/-- Whether a dotted identifier looks like a declaration name: see the module docstring. -/
def looksLikeName : List String → Bool
  | [] => false
  | [s] => ((s.splitOn "_").filter (·.length ≥ 2)).length ≥ 2 || isCamel s
  | segs@(s :: _) =>
    segs.getLast? != some "lean" && ((segs.getLast?.map String.length).getD 0) ≥ 2 &&
      s.length ≥ 2 && !(s.toList.head?.any Char.isLower && s.length ≤ 2) &&
      !(s.startsWith "h" && s.length ≤ 3)

/-- Words of the README that are not names of the environment: a Lake executable and a Lake
option, a tactic, Mathlib's test library and the library of another project. -/
def notNames : List String :=
  ["mk_all", "allowNonModules", "native_decide", "MathlibTest", "DerivedAlgGeo"]

/-- The paths of a text that end in `.lean`, with the line (from `0`) each is on. A path split as
`` `A/` `B.lean` `` or over two lines after a `/` is joined, and `A/{B,C}.lean` is expanded. -/
def leanPaths (s : String) : Array (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut line := 0
  let mut cur : List Char := []
  let mut depth := 0
  let mut i := 0
  while i ≤ cs.size do
    let c := cs[i]?.getD ' '
    if c == '/' then
      -- the path goes on after `` /` ` `` or a line break
      let tick := cs[i + 1]? == some '`'
      let mut j := if tick then i + 2 else i + 1
      while cs[j]? == some ' ' || cs[j]? == some '\n' do j := j + 1
      if (tick && j > i + 2 && cs[j]? == some '`') || cs[i + 1]? == some '\n' then
        let next := if tick then j + 1 else j
        line := line + ((cs.extract i next).toList.filter (· == '\n')).length
        cur := c :: cur
        i := next
        continue
    if c.isAlphanum || c == '_' || c == '/' || c == '.' || c == '-' || c == '{' ||
        ((c == '}' || c == ',') && depth > 0) then
      if c == '{' then depth := depth + 1
      if c == '}' then depth := depth - 1
      cur := c :: cur
    else
      let w := String.ofList (cur.dropWhile (· ∈ ['.', ',', '-'])).reverse
      let ws := match w.splitOn "{" with
        | [pre, rest] => match rest.splitOn "}" with
          | [alts, post] => (alts.splitOn ",").map (pre ++ · ++ post)
          | _ => [w]
        | _ => [w]
      for p in ws do
        if p.endsWith ".lean" && p.length > 5 then out := out.push (p, line)
      cur := []
      depth := 0
      if c == '\n' then line := line + 1
    i := i + 1
  return out

/-- The namespaces opened by `open` commands of a Lean source. -/
def opens (src : String) : Array Name := Id.run do
  let mut out := #[]
  for l in src.splitOn "\n" do
    if let "open" :: rest := (l.splitOn " ").filter (· ≠ "") then
      for w in rest.takeWhile fun w => w ∉ ["in", "hiding", "renaming"] && !w.startsWith "(" do
        unless w == "scoped" do out := out.push w.toName
  return out

/-- The names and files a resolution can use. -/
structure Ctx where
  env : Environment
  /-- Every imported constant, private ones under their user name. -/
  known : NameSet
  /-- Constants and their namespaces, by last component, for lookup by suffix. -/
  byLast : Std.HashMap String (Array Name)
  options : NameSet
  /-- The test modules, without the prefix `K3TwistsTest`. -/
  tests : NameSet
  /-- The `.lean` files of the library, its tests, these scripts and Mathlib, from `src/lean`. -/
  files : Array String

/-- Whether `n` is a constant, namespace, module, test module, option or keyword. -/
def names (ctx : Ctx) (n : Name) : Bool :=
  ctx.known.contains n || ctx.env.isNamespace n || (ctx.env.getModuleIdx? n).isSome ||
    ctx.tests.contains n || ctx.options.contains n ||
    ((Parser.getTokenTable ctx.env).find? n.toString).isSome

/-- A constant or namespace whose last components are those of `n`, one of the library if there
is one. -/
def bySuffix (ctx : Ctx) (n : Name) : Option Name :=
  let found := (ctx.byLast.getD n.lastComponentAsString #[]).filter fun c =>
    c.components.drop (c.components.length - n.components.length) == n.components
  let inLib (c : Name) := ((ctx.env.getModuleIdxFor? c).map fun i =>
    (`K3Twists).isPrefixOf ctx.env.header.moduleNames[i.toNat]!).getD false
  found.find? inLib <|> found[0]?

/-- What `n` names under one of `pre`: a name that is not deprecated if there is one; otherwise,
by suffix or as field notation `a.f` on a constant `a` that is not a namespace, with a note. -/
def resolve (ctx : Ctx) (pre : Array Name) (n : Name) : Option (Name × Option String) :=
  let found := pre.filterMap fun p => if names ctx (p ++ n) then some (p ++ n) else none
  match (found.find? fun c => !Linter.isDeprecated ctx.env c) <|> found[0]? with
  | some c => some (c, none)
  | none => match bySuffix ctx n with
    | some c => some (c, some s!"is `{c}`")
    | none =>
      let cs := n.components
      (List.range (cs.length - 1)).findSome? fun k =>
        let head := (cs.take (k + 1)).foldl (· ++ ·) .anonymous
        if pre.any fun p => ctx.known.contains (p ++ head) && !ctx.env.isNamespace (p ++ head) then
          (bySuffix ctx ((cs.drop (k + 1)).foldl (· ++ ·) .anonymous)).map
            (·, some "reads as field notation")
        else none

/-- The errors and notes found, and the number of names and paths checked. -/
structure Report where
  errors : Array String := #[]
  notes : Array String := #[]
  names : Nat := 0
  paths : Nat := 0

/-- Check the names and paths of a docstring or of the README. `file` is the citing file, from
`src/lean`, `line₀` the line the text starts on, and `pre` the namespaces to resolve under (none
for the README). -/
def checkText (ctx : Ctx) (file : System.FilePath) (line₀ : Nat) (pre : Array Name)
    (text : String) (r : Report) : IO Report := do
  let mut r := r
  let lines := (text.splitOn "\n").toArray
  let mentions (t : String) := (t.splitOn "deprecated").length > 1
  -- a docstring that says "deprecated" may cite deprecated names; in the README, only the lines
  -- next to the word may
  let saysDeprecated (l : Nat) :=
    if pre.isEmpty then [l - 1, l, l + 1].any (mentions <| lines[·]?.getD "") else mentions text
  for (span, l) in codeSpans text do
    if (span.splitOn ".lean").length > 1 then continue
    for segs in identWords span do
      unless looksLikeName segs && !notNames.contains (".".intercalate segs) do continue
      let n := (if segs.head? == some "_root_" then segs.tail else segs).foldl .str .anonymous
      r := { r with names := r.names + 1 }
      let loc := s!"{file}:{line₀ + l}: `{n}`"
      match resolve ctx (pre.push .anonymous) n with
      | none => r := { r with errors := r.errors.push s!"{loc} names nothing" }
      | some (c, note) =>
        if let some note := note then
          unless pre.isEmpty do r := { r with notes := r.notes.push s!"{loc} {note}" }
        if Linter.isDeprecated ctx.env c && !saysDeprecated l then
          r := { r with errors := r.errors.push s!"{loc} is deprecated" }
  let dirs := (file.parent.map fun d => (List.range d.components.length).map fun k =>
    System.mkFilePath (d.components.take (d.components.length - k))).getD []
  for (p, l) in leanPaths text do
    let loc := s!"{file}:{line₀ + l}: `{p}`"
    r := { r with paths := r.paths + 1 }
    let mut ok := false
    for d in dirs ++ [("K3Twists" : System.FilePath), ".", ".lake/packages/mathlib"] do
      if ← (d / p).pathExists then ok := true
    unless ok do
      match ctx.files.find? (·.endsWith ("/" ++ p)) with
      | some f => r := { r with notes := r.notes.push s!"{loc} is `{f}`" }
      | none => r := { r with errors := r.errors.push s!"{loc} is no file" }
  return r

end CheckDocNames

open CheckDocNames in
run_cmd do
  let env ← getEnv
  let mut known : NameSet := {}
  let mut seen : NameSet := {}
  let mut byLast : Std.HashMap String (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    for c in env.header.moduleData[i]!.constNames do
      let c := privateToUserName c
      if c.isInternal then continue
      known := known.insert c
      let mut p := c
      while !p.isAnonymous && !seen.contains p do
        seen := seen.insert p
        byLast := byLast.insert p.lastComponentAsString
          ((byLast.getD p.lastComponentAsString #[]).push p)
        p := p.getPrefix
  let mut files := #[]
  let mut tests : NameSet := {}
  for d in ["K3Twists", "K3TwistsTest", "scripts", ".lake/packages/mathlib/Mathlib"] do
    for f in ← System.FilePath.walkDir d do
      if f.extension != some "lean" then continue
      files := files.push f.toString
      if d == "K3TwistsTest" then
        tests := tests.insert ((f.withExtension "").components.drop 1 |>.foldl .str .anonymous)
  let options := (← getOptionDecls).foldl (fun s n _ => s.insert n) {}
  let ctx : Ctx := { env, known, byLast, options, tests, files }
  let mut r : Report := {}
  let mut modules : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`K3Twists).isPrefixOf m do continue
    modules := modules + 1
    let file := (System.mkFilePath (m.components.map toString)).addExtension "lean"
    let src ← IO.FS.readFile file
    let lines := (src.splitOn "\n").toArray
    let mut spaces : NameSet := (opens src).foldl NameSet.insert {}
    for c in env.header.moduleData[i]!.constNames do
      let mut p := (privateToUserName c).getPrefix
      while !p.isAnonymous do
        spaces := spaces.insert p
        p := p.getPrefix
    let pre := spaces.toArray
    for d in (getModuleDoc? env m).getD #[] do
      -- the text of a `/-!` that ends its line starts on the next line
      let l := d.declarationRange.pos.line
      let opener := (lines[l - 1]?.getD "").toList.reverse.dropWhile (· == ' ')
      r ← checkText ctx file (if opener.take 3 == ['!', '-', '/'] then l + 1 else l) pre d.doc r
    for (c, doc) in docStringExt.getModuleEntries (level := .server) env i do
      let l := ((declRangeExt.find? (level := .server) env c).map (·.range.pos.line)).getD 0
      r ← checkText ctx file l pre doc r
  r ← checkText ctx "README.md" 1 #[] (← IO.FS.readFile "README.md") r
  if modules == 0 then throwError "no K3Twists module is in the environment"
  if (← IO.getEnv "CHECK_DOC_NAMES_NOTES").isSome then
    logInfo m!"{r.notes.size} notes:\n{"\n".intercalate r.notes.toList}"
  unless r.errors.isEmpty do
    throwError m!"{r.errors.size} cited names or paths do not exist or are deprecated:\n\
      {"\n".intercalate r.errors.toList}"
  logInfo m!"the {r.names} names and {r.paths} paths cited in the docstrings of {modules} modules \
    and in README.md exist ({r.notes.size} notes)"
