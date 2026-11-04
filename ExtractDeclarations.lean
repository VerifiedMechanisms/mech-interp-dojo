/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
-- extract-declarations: skip-this-file
import Lean

/-!
# Declaration extractor

A Lean metaprogram that reads Lean source files and writes two JSON files:

* `definitions.json`: every definition (`def`, `abbrev`, `instance`, `opaque`, `structure`,
  `class`, `inductive`) with its name, type, and the definition assigned to the name;
* `theorems.json`: every theorem (`theorem`, `lemma`) with its name and the statement it proves.
  Proofs are never written.

## Usage

Run it from the root of the Lake project whose files you want to read, so that the project's
build products and dependencies (e.g. Mathlib) can be found:

```
lake env lean --run ExtractDeclarations.lean [OPTIONS] PATH...
```

Each `PATH` can be a `.lean` file, a directory (searched recursively; hidden directories such as
`.lake` and `.git` are skipped), or the root of a Lean project. Options:

* `-o, --out-dir DIR`: directory for the output files (default: `.`)
* `--definitions FILE`: path of the definitions JSON (default: `DIR/definitions.json`)
* `--theorems FILE`: path of the theorems JSON (default: `DIR/theorems.json`)
* `--mode auto|import|elab`: how to obtain declarations (default: `auto`)
  - `import`: load the files' existing compiled `.olean`s (fast; run `lake build` first);
  - `elab`: elaborate each file from source (slow: each file re-imports its dependencies);
  - `auto`: run `lake build` on the files that belong to the current project, load the
    `.olean` of every file that has one, and elaborate the rest.
* `--no-build`: in `auto` mode, skip `lake build` and trust the existing `.olean`s
* `--no-lake`: in `elab` mode, do not ask `lake setup-file` for the file's imports and options
* `--no-source`: leave out the verbatim `source` field of definitions
* `--exclude PATH`: skip a file or every file under a directory (repeatable)
* `-D NAME=VALUE`: set a Lean option, used for elaboration and pretty-printing
  (e.g. `-D pp.proofs=true` to print proof terms inside definition bodies)
* `-v, --verbose`: report progress and elaboration warnings on stderr

Each output file holds a JSON array sorted by file and line. A definition object has the fields
`name`, `kind`, `type`, `value` (the elaborated body, pretty-printed: for a recursive definition
the right-hand side of its unfolding equation, for an inductive type or structure its
constructors), `source` (the declaration exactly as written in the file), and location metadata.
A theorem object has `name`, `kind`, `type` (the statement as a closed term), `signature` (the
statement with its binders shown as named arguments), and location metadata.

Only declarations written in the files are reported. Declarations that Lean generates
(constructors, recursors, structure projections, matchers, equation lemmas, `@[ext]` and
`@[simps]` lemmas, and so on) are left out.

Files containing the line `-- extract-declarations: skip-this-file` are skipped, so running the
extractor on its own project does not report the extractor itself.
-/

open Lean Elab Meta System

namespace ExtractDeclarations

/-! ## Configuration and command-line parsing -/

/-- How the declarations of a file are obtained. -/
inductive Mode where
  /-- Use the compiled `.olean` when it is up to date, otherwise elaborate the source. -/
  | auto
  /-- Always use the compiled `.olean`. -/
  | compiled
  /-- Always elaborate the source file. -/
  | source
  deriving BEq, Inhabited

/-- Command-line configuration. -/
structure Config where
  inputs : Array FilePath := #[]
  outDir : FilePath := "."
  definitionsFile? : Option FilePath := none
  theoremsFile? : Option FilePath := none
  mode : Mode := .auto
  useLake : Bool := true
  build : Bool := true
  includeSource : Bool := true
  excludes : Array FilePath := #[]
  /-- Raw `-D` options; their types are inferred from the values. -/
  rawOptions : Array (Name × String) := #[]
  verbose : Bool := false
  deriving Inhabited

/-- The line marking a file that should not be read. -/
def skipMarker : String := "-- extract-declarations: skip-this-file"

def usage : String :=
  "usage: lake env lean --run ExtractDeclarations.lean [OPTIONS] PATH...

PATH is a .lean file, a directory, or a Lean project root.

options:
  -o, --out-dir DIR         output directory (default: .)
      --definitions FILE    definitions JSON path (default: DIR/definitions.json)
      --theorems FILE       theorems JSON path (default: DIR/theorems.json)
      --mode MODE           auto | import | elab (default: auto)
      --no-build            in auto mode, do not run `lake build` first
      --no-lake             in elab mode, do not call `lake setup-file`
      --no-source           omit the verbatim `source` field of definitions
      --exclude PATH        skip a file or directory (repeatable)
  -D NAME=VALUE             set a Lean option (e.g. -D pp.proofs=true)
  -v, --verbose             report progress and warnings on stderr
  -h, --help                show this message"

/-- Turn `-D` strings into `Options`, guessing each value's type from its spelling. -/
def Config.options (cfg : Config) : Options :=
  cfg.rawOptions.foldl (init := {}) fun opts (k, v) =>
    if v == "true" then opts.insert k (.ofBool true)
    else if v == "false" then opts.insert k (.ofBool false)
    else if let some n := v.toNat? then opts.insert k (.ofNat n)
    else opts.insert k (.ofString v)

partial def parseArgs (args : List String) (cfg : Config := {}) : Except String Config :=
  match args with
  | [] => if cfg.inputs.isEmpty then .error "no input paths given" else .ok cfg
  | "-o" :: dir :: rest | "--out-dir" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | "--definitions" :: f :: rest => parseArgs rest { cfg with definitionsFile? := some f }
  | "--theorems" :: f :: rest => parseArgs rest { cfg with theoremsFile? := some f }
  | "--mode" :: m :: rest =>
    match m with
    | "auto" => parseArgs rest { cfg with mode := .auto }
    | "import" => parseArgs rest { cfg with mode := .compiled }
    | "elab" => parseArgs rest { cfg with mode := .source }
    | _ => .error s!"unknown mode '{m}' (expected auto, import or elab)"
  | "--no-lake" :: rest => parseArgs rest { cfg with useLake := false }
  | "--no-build" :: rest => parseArgs rest { cfg with build := false }
  | "--no-source" :: rest => parseArgs rest { cfg with includeSource := false }
  | "--exclude" :: p :: rest => parseArgs rest { cfg with excludes := cfg.excludes.push p }
  | "-D" :: kv :: rest => do
    let some i := kv.toList.idxOf? '='
      | .error s!"expected NAME=VALUE after -D, got '{kv}'"
    let k := String.ofList (kv.toList.take i)
    let v := String.ofList (kv.toList.drop (i + 1))
    parseArgs rest { cfg with rawOptions := cfg.rawOptions.push (k.toName, v) }
  | "-v" :: rest | "--verbose" :: rest => parseArgs rest { cfg with verbose := true }
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown option '{arg}'"
    else parseArgs rest { cfg with inputs := cfg.inputs.push arg }

/-! ## Finding source files -/

/-- A Lean source file together with what we know about it. -/
structure SourceFile where
  /-- Canonical absolute path. -/
  path : FilePath
  /-- Path shown in the output (relative to the working directory when possible). -/
  display : String
  contents : String
  fileMap : FileMap
  /-- Module name, inferred from `LEAN_SRC_PATH`. -/
  module? : Option Name

def isLakefile (p : FilePath) : Bool :=
  p.fileName == some "lakefile.lean"

/-- Directories that never contain sources of the project itself. -/
def skipDir (p : FilePath) : Bool :=
  match p.fileName with
  | some n => n.startsWith "." || n == "lake-packages"
  | none => false

/-- All `.lean` files at or under `p`. -/
def collectLeanFiles (p : FilePath) : IO (Array FilePath) := do
  if ← p.isDir then
    let files ← p.walkDir (enter := fun d => pure !(skipDir d))
    return files.filter fun f => f.extension == some "lean" && !isLakefile f
  else if ← p.pathExists then
    if p.extension == some "lean" then return #[p]
    throw <| IO.userError s!"not a Lean file: {p}"
  else
    throw <| IO.userError s!"no such file or directory: {p}"

def realPath (p : FilePath) : IO FilePath :=
  return (← IO.FS.realPath p).normalize

/-- `p` with `root` removed from its front, if `root` is a prefix of `p` (as directories). -/
def relativeTo? (p root : FilePath) : Option FilePath :=
  let r := root.toString
  let r := if r.endsWith FilePath.pathSeparator.toString then r
    else r ++ FilePath.pathSeparator.toString
  if r.isPrefixOf p.toString then some ⟨String.ofList (p.toString.toList.drop r.length)⟩
  else none

/-- Whether a compiled `.olean` of `mod` is on the search path (`LEAN_PATH`). -/
def hasOLean (mod : Name) : IO Bool := do
  let some olean ← (← searchPathRef.get).findWithExt "olean" mod | return false
  olean.pathExists

/--
Find the module name of `path` from the source roots in `LEAN_SRC_PATH` (set by `lake env`).
Roots are tried from the most to the least specific, and a root whose module has a compiled
`.olean` is preferred, so that a library with `srcDir = "foo"` gets `Foo.Bar`, not `foo.Foo.Bar`.
-/
def findModule (path : FilePath) : IO (Option Name) := do
  let roots ← (← getSrcSearchPath).filterMapM fun r => do
    try return some (← realPath r) catch _ => return none
  let candidates := roots.filterMap fun r => relativeTo? path r
  let candidates := candidates.toArray.qsort (·.toString.length < ·.toString.length)
  let mods := candidates.map fun rel =>
    (rel.withExtension "").components.foldl Name.mkStr .anonymous
  for mod in mods do
    if ← hasOLean mod then return some mod
  return mods[0]?

def loadSourceFile (path : FilePath) : IO SourceFile := do
  let contents ← IO.FS.readFile path
  let cwd ← realPath (← IO.currentDir)
  let display := (relativeTo? path cwd).getD path |>.toString
  let module? ← findModule path
  return { path, display, contents, fileMap := contents.toFileMap, module? }

def hasSkipMarker (contents : String) : Bool :=
  (contents.splitOn "\n").any (·.trimAscii.toString == skipMarker)

/-- Expand the inputs into a deduplicated list of source files. -/
def collectSources (cfg : Config) : IO (Array SourceFile) := do
  let excludes ← cfg.excludes.filterMapM fun p => do
    try return some (← realPath p) catch _ => return none
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for input in cfg.inputs do
    for f in ← collectLeanFiles input do
      let f ← realPath f
      if seen.contains f.toString then continue
      seen := seen.insert f.toString
      if excludes.any fun e => e == f || (relativeTo? f e).isSome then continue
      let sf ← loadSourceFile f
      if hasSkipMarker sf.contents then
        if cfg.verbose then IO.eprintln s!"skipping {sf.display} (marked skip-this-file)"
        continue
      out := out.push sf
  return out

/-! ## Obtaining an environment for a file -/

unsafe def enableInitializersUnsafe : IO Unit := enableInitializersExecution

/--
Allow imported modules to run their `initialize` declarations (needed e.g. for Mathlib's
environment extensions). Lean switches this off again after every import, so it is called
before each one.
-/
@[implemented_by enableInitializersUnsafe] opaque enableInitializers : IO Unit

/-- The innermost directory containing `start` that holds a Lake configuration file. -/
partial def findLakeRoot (start : FilePath) : IO (Option FilePath) := do
  let some dir := start.parent | return none
  go dir
where
  go (dir : FilePath) : IO (Option FilePath) := do
    if (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) then
      return some dir
    match dir.parent with
    | some p => if p == dir then return none else go p
    | none => return none

/-- Run `lake` with the given arguments in `root`; returns whether it succeeded. -/
def runLake (cfg : Config) (root : FilePath) (args : Array String) : IO Bool := do
  if cfg.verbose then
    let shown := if args.size > 4 then s!"{args[0]!} <{args.size - 1} modules>"
      else " ".intercalate args.toList
    IO.eprintln s!"running `lake {shown}` in {root}"
  let out ← try IO.Process.output { cmd := "lake", args, cwd := root }
    catch e =>
      IO.eprintln s!"warning: could not run lake: {e}"
      return false
  if cfg.verbose && out.exitCode != 0 then IO.eprint (out.stdout ++ out.stderr)
  return out.exitCode == 0

/--
Bring the `.olean`s of the given modules up to date with `lake build`. If the build fails (e.g.
one module has errors), find out module by module which `.olean`s are up to date anyway.
Returns the modules whose `.olean` is up to date.
-/
def buildModules (cfg : Config) (root : FilePath) (mods : Array Name) : IO (Array Name) := do
  if mods.isEmpty then return #[]
  let names := mods.map (·.toString (escape := false))
  if ← runLake cfg root (#["build"] ++ names) then return mods
  IO.eprintln s!"warning: `lake build` failed in {root}; checking modules one at a time"
  mods.filterM fun m => runLake cfg root #["build", "--no-build", m.toString (escape := false)]

/--
Ask Lake for the module setup (name, imports, options from the lakefile) of a file. This also
builds the file's imports when they are out of date.
-/
def lakeSetup? (cfg : Config) (sf : SourceFile) : IO (Option ModuleSetup) := do
  let some root ← findLakeRoot sf.path | return none
  if cfg.verbose then IO.eprintln s!"  asking Lake (in {root}) to set up {sf.display}"
  let out ← try
      IO.Process.output { cmd := "lake", args := #["setup-file", sf.path.toString], cwd := root }
    catch e =>
      IO.eprintln s!"warning: could not run `lake setup-file` for {sf.display}: {e}"
      return none
  if out.exitCode != 0 then
    IO.eprintln s!"warning: `lake setup-file` failed for {sf.display}:\n{out.stderr}"
    return none
  match Json.parse out.stdout >>= fromJson? with
  | .ok setup => return some setup
  | .error e =>
    IO.eprintln s!"warning: could not read the output of `lake setup-file`: {e}"
    return none

/-- Print the messages of an elaboration run; errors always, the rest only if `verbose`. -/
def reportMessages (cfg : Config) (msgs : MessageLog) : IO Bool := do
  let mut hasErrors := false
  for msg in msgs.toList do
    if msg.severity == .error then hasErrors := true
    if msg.severity == .error || cfg.verbose then
      IO.eprint (← msg.toString (includeEndPos := false))
  return hasErrors

/--
Elaborate a source file the way `lean` does and return the resulting environment.
Declarations of the file are the constants added on top of its imports.
-/
def elabFile (cfg : Config) (sf : SourceFile) : IO Environment := do
  let setup? ← if cfg.useLake then lakeSetup? cfg sf else pure none
  enableInitializers
  let inputCtx := Parser.mkInputContext sf.contents sf.path.toString
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet cfg.options true
  let mainModuleName := sf.module?.getD `_extracted
  let setup (stx : HeaderSyntax) : Language.ProcessingT IO
      (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
    if let some setup := setup? then
      liftM <| setup.dynlibs.forM Lean.loadDynlib
      return .ok {
        package? := setup.package?
        mainModuleName := setup.name
        isModule := strictOr setup.isModule stx.isModule
        imports := setup.imports?.getD stx.imports
        plugins := setup.plugins
        importArts := setup.importArts
        -- options given on our command line override the ones from the lakefile
        opts := setup.options.toOptions.mergeBy (fun _ _ ours => ours) opts
      }
    else
      return .ok { imports := stx.imports, isModule := stx.isModule, mainModuleName, opts }
  let snap ← Language.Lean.process setup none { inputCtx with }
  let snaps := Language.toSnapshotTree snap
  let msgs := snaps.getAll.foldl (init := (.empty : MessageLog)) (· ++ ·.diagnostics.msgLog)
  if ← reportMessages cfg msgs then
    IO.eprintln s!"warning: {sf.display} has errors; declarations that failed to elaborate \
      are missing from the output"
  let some cmdState := Language.Lean.waitForFinalCmdState? snap
    | throw <| IO.userError s!"could not process the imports of {sf.display}"
  return cmdState.env

/-- Import the given compiled modules into one environment. -/
def importEnv (cfg : Config) (mods : Array Name) : IO Environment := do
  enableInitializers
  importModules (mods.map fun m => { module := m }) cfg.options (loadExts := true)

/-! ## Turning constants into records -/

/-- Which output file a declaration goes to. -/
inductive Category where
  | definition
  | theorem
  deriving BEq

/-- A declaration ready to be written out. -/
structure Record where
  category : Category
  name : Name
  file : String
  line : Nat
  /-- The JSON object's fields, in output order. -/
  fields : List (String × Json)

def runMeta (env : Environment) (opts : Options) (x : MetaM α) : IO α := do
  let ctx : Core.Context := {
    fileName := "<extract-declarations>", fileMap := default, options := opts,
    maxHeartbeats := 0, maxRecDepth := maxRecDepth.get opts }
  Prod.fst <$> (x.run' {} {}).toIO ctx { env }

def ppE (e : Expr) : MetaM String := do
  try return toString (← ppExpr e)
  catch ex => return s!"<failed to pretty-print: {← ex.toMessageData.toString}>"

/-- The source text between two positions. -/
def sourceSlice (sf : SourceFile) (r : DeclarationRange) : String :=
  let b := sf.fileMap.ofPosition r.pos
  let e := sf.fileMap.ofPosition r.endPos
  String.Pos.Raw.extract sf.contents b e

/-- The components of a name as it is written at a declaration site. -/
def writtenComponents (s : String) : List String :=
  let parts := (s.splitOn ".").map fun c => (c.replace "«" "").replace "»" ""
  match parts with
  | "_root_" :: rest => rest
  | parts => parts

def nameComponents (n : Name) : List String :=
  n.components.map (·.toString (escape := false))

/--
Whether a constant was written in the file rather than generated by Lean, returning its
declaration ranges if so. A written declaration has a name token inside its declaration whose
text ends the declaration's full name. This rules out e.g. `Foo.ext_iff` (whose name token is
`Foo`), `@[simps]` lemmas, and `@[ext]` lemmas (whose name token is the attribute).
-/
def isWritten (sf : SourceFile) (n : Name) (ci : ConstantInfo) : MetaM (Option DeclarationRanges) := do
  let env ← getEnv
  let userName := privateToUserName n
  if userName.isInternalDetail || userName.isInternal then return none
  match ci with
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return none
  | _ => pure ()
  if isAuxRecursor env n || isNoConfusion env n || isRecCore env n || isMatcherCore env n ||
      (← isProjectionFn n) then
    return none
  let some ranges ← findDeclarationRanges? n | return none
  -- A written declaration contains its name token and more (at least a keyword). Generated
  -- declarations often point both ranges at one token, e.g. `ext` in `@[ext]`.
  let ⟨r, sel⟩ := ranges
  if sel.pos.lt r.pos || r.endPos.lt sel.endPos || (r.pos == sel.pos && r.endPos == sel.endPos)
  then return none
  let written := writtenComponents (sourceSlice sf sel).trimAscii.toString
  let nameMatches := !written.isEmpty &&
    (nameComponents userName).reverse.take written.length == written.reverse
  if nameMatches then return some ranges
  -- anonymous instances get generated names; keep them when written with `instance`
  -- (this rules out instances generated by `deriving`, whose range is just the class name)
  if isInstanceCore env n && ((sourceSlice sf r).splitOn "instance").length > 1 then
    return some ranges
  return none

def declKind (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ =>
    if isClass env n then "class"
    else if isStructure env n then "structure"
    else "inductive"
  | .defnInfo d =>
    if isInstanceCore env n then "instance"
    else if d.safety == .partial then "partial def"
    else if d.safety == .unsafe then "unsafe def"
    else if getReducibilityStatusCore env n matches .reducible then "abbrev"
    else "def"
  | _ => "other"

/-- The definition assigned to a name, pretty-printed. -/
def definitionValue (n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  match ci with
  | .defnInfo d =>
    -- A recursive definition is compiled to a recursor or fixpoint; its unfolding equation
    -- states the definition as written.
    let eqn? ← try getUnfoldEqnFor? n (nonRec := false) catch _ => pure none
    if let some eqn := eqn? then
      let eqnTy := (← getConstInfo eqn).type
      let body? ← forallTelescope eqnTy fun xs eq => do
        let some (_, _, rhs) := eq.eq? | return none
        return some (← mkLambdaFVars xs rhs)
      if let some body := body? then return some (← ppE body)
    return some (← ppE d.value)
  | .opaqueInfo o => return some (← ppE o.value)
  | .inductInfo i =>
    -- `ppSignature` keeps the constructor's argument names, i.e. a structure's field names
    let ctors ← i.ctors.mapM fun c => do
      try return s!"| {(← PrettyPrinter.ppSignature c).fmt}"
      catch _ => return s!"| {privateToUserName c} : {← ppE (← getConstInfo c).type}"
    return some ("\n".intercalate ctors)
  | _ => return none

def rangeFields (r : DeclarationRange) : List (String × Json) :=
  [("line", r.pos.line), ("column", r.pos.column),
   ("endLine", r.endPos.line), ("endColumn", r.endPos.column)]

def recordOf (cfg : Config) (sf : SourceFile) (module : Name) (n : Name) (ci : ConstantInfo) :
    MetaM (Option Record) := do
  let some ranges ← isWritten sf n ci | return none
  let env ← getEnv
  let userName := privateToUserName n
  let kind := declKind env n ci
  let type ← ppE ci.type
  let common : List (String × Json) := [
    ("name", toJson userName.toString),
    ("kind", kind),
    ("type", type)]
  let location : List (String × Json) := [
    ("isPrivate", toJson (isPrivateName n)),
    ("module", if module.isAnonymous then Json.null else toJson module.toString),
    ("file", toJson sf.display)] ++ rangeFields ranges.range
  let isProp ← try isProp ci.type catch _ => pure false
  if ci matches .thmInfo _ || (ci matches .axiomInfo _ && isProp) then
    let signature ← try pure (toString (← PrettyPrinter.ppSignature n).fmt) catch _ => pure type
    return some {
      category := .theorem, name := userName, file := sf.display, line := ranges.range.pos.line
      fields := common ++ [("signature", toJson signature)] ++ location }
  let value ← definitionValue n ci
  let source := if cfg.includeSource then toJson (sourceSlice sf ranges.range) else Json.null
  let flags : List (String × Json) :=
    [("isNoncomputable", isNoncomputable env n),
     ("universeParams", toJson (ci.levelParams.map (·.toString)))]
  return some {
    category := .definition, name := userName, file := sf.display, line := ranges.range.pos.line
    fields := common ++ [("value", toJson value)] ++
      (if cfg.includeSource then [("source", source)] else []) ++ flags ++ location }

/-- Records for the given constants of a file. -/
def recordsOf (cfg : Config) (env : Environment) (sf : SourceFile) (module : Name)
    (names : Array Name) : IO (Array Record) :=
  runMeta env cfg.options do
    let mut out := #[]
    for n in names do
      let some ci := env.find? n | continue
      let r? ← try recordOf cfg sf module n ci
        catch e => do
          IO.eprintln s!"warning: skipping {n}: {← e.toMessageData.toString}"
          pure none
      if let some r := r? then out := out.push r
    return out

/-! ## Driver -/

/-- Records for files read from their `.olean`s, all imported into one environment. -/
def processImported (cfg : Config) (files : Array (SourceFile × Name)) : IO (Array Record) := do
  if files.isEmpty then return #[]
  if cfg.verbose then IO.eprintln s!"importing {files.size} compiled module(s)"
  let envs ← try
      let env ← importEnv cfg (files.map (·.2))
      pure (files.map fun _ => env)
    catch e =>
      -- e.g. two of the modules declare the same name: import them one at a time
      if cfg.verbose then IO.eprintln s!"joint import failed ({e}); importing one at a time"
      files.mapM fun (_, m) => importEnv cfg #[m]
  let mut out := #[]
  for (sf, mod) in files, env in envs do
    let some idx := env.getModuleIdx? mod
      | IO.eprintln s!"warning: module {mod} missing after import"; continue
    let some data := env.header.moduleData[idx.toNat]?
      | IO.eprintln s!"warning: no data for module {mod}"; continue
    out := out ++ (← recordsOf cfg env sf mod data.constNames)
  return out

/-- Records for one file elaborated from source. -/
def processElaborated (cfg : Config) (sf : SourceFile) : IO (Array Record) := do
  if cfg.verbose then IO.eprintln s!"elaborating {sf.display}"
  let env ← elabFile cfg sf
  let names := env.constants.map₂.foldl (init := #[]) fun acc n _ => acc.push n
  recordsOf cfg env sf (sf.module?.getD .anonymous) names

def writeJson (path : FilePath) (records : Array Record) : IO Unit := do
  if let some dir := path.parent then
    if !dir.toString.isEmpty then IO.FS.createDirAll dir
  -- written by hand (rather than with `Json.pretty`) to keep the fields in a readable order
  let render (r : Record) : String :=
    let fields := r.fields.map fun (k, v) => s!"    {(toJson k).compress}: {v.compress}"
    "  {\n" ++ ",\n".intercalate fields ++ "\n  }"
  let body := if records.isEmpty then "[]"
    else "[\n" ++ ",\n".intercalate (records.map render).toList ++ "\n]"
  IO.FS.writeFile path (body ++ "\n")

def run (cfg : Config) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sources ← collectSources cfg
  if sources.isEmpty then
    IO.eprintln "no Lean files found"
    return 1
  let mut imported := #[]
  let mut elaborated := #[]
  if cfg.mode == .source then
    elaborated := sources
  else
    -- In auto mode, build the files of the current project first, so that their `.olean`s
    -- match the sources. Files that do not build are elaborated instead (reporting errors).
    let mut stale : Std.HashSet Name := {}
    if cfg.mode == .auto && cfg.build then
      if let some root ← findLakeRoot ((← realPath (← IO.currentDir)) / "_") then
        let mut mods := #[]
        for sf in sources do
          if let some mod := sf.module? then
            if (← findLakeRoot sf.path) == some root then mods := mods.push mod
        let fresh ← buildModules cfg root mods
        stale := mods.foldl (init := {}) fun acc m => if fresh.contains m then acc else acc.insert m
    for sf in sources do
      if let some mod := sf.module? then
        if !stale.contains mod && (← hasOLean mod) then
          imported := imported.push (sf, mod)
          continue
      if cfg.mode == .compiled then
        IO.eprintln s!"error: no .olean for {sf.display}; run `lake build` first, \
          or use --mode auto or --mode elab"
        return 1
      elaborated := elaborated.push sf
  let mut records ← processImported cfg imported
  for sf in elaborated do
    try
      records := records ++ (← processElaborated cfg sf)
    catch e =>
      IO.eprintln s!"error: failed to process {sf.display}: {e}"
  let sorted := records.qsort fun a b =>
    a.file < b.file || (a.file == b.file && (a.line < b.line ||
      (a.line == b.line && a.name.toString < b.name.toString)))
  let defs := sorted.filter (·.category == .definition)
  let thms := sorted.filter (·.category == .theorem)
  let defsPath := cfg.definitionsFile?.getD (cfg.outDir / "definitions.json")
  let thmsPath := cfg.theoremsFile?.getD (cfg.outDir / "theorems.json")
  writeJson defsPath defs
  writeJson thmsPath thms
  IO.println s!"read {sources.size} file(s) ({imported.size} from .olean, \
    {elaborated.size} elaborated)"
  IO.println s!"wrote {defs.size} definition(s) to {defsPath}"
  IO.println s!"wrote {thms.size} theorem(s) to {thmsPath}"
  return 0

end ExtractDeclarations

unsafe def main (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then
    IO.println ExtractDeclarations.usage
    return 0
  match ExtractDeclarations.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n\n{ExtractDeclarations.usage}"
    return 2
  | .ok cfg =>
    enableInitializersExecution
    try ExtractDeclarations.run cfg
    catch e =>
      IO.eprintln s!"error: {e}"
      return (1 : UInt32)
