/-
  Lego.Cubical.Module: Module System for definitions and imports

  Implements a simple module system with:
  - File-based module organization (module = file)
  - Import declarations with visibility control
  - Export lists for public definitions
  - Namespace management for qualified names
  - Dependency tracking for incremental compilation

  Mathematical structure:
  - Modules form a category where morphisms are imports
  - Module composition via qualified name resolution
  - Dependency DAG for build ordering

  Based on redtt's module system (FileRes, ResEnv, Importer)
-/

import Cubical.Core
import Cubical.GlobalEnv
import Cubical.Elaborate
import Std.Data.HashMap

namespace Lego.Cubical.Module

open Lego.Core
open Lego.Cubical

/-! ## Module Paths

    Modules are identified by selector paths like ["prelude", "path"]
-/

/-- A module path (e.g., ["prelude", "path"] for prelude.path) -/
abbrev Selector := List String

/-- Convert selector to dotted string -/
def selectorToPath (sel : Selector) : String :=
  ".".intercalate sel

/-- Parse dotted string to selector -/
def selectorFromPath (path : String) : Selector :=
  path.splitOn "."

/-- Convert to file path with extension -/
def selectorToFilePath (base : String) (sel : Selector) (ext : String := ".lego") : String :=
  let parts := sel.map fun s => s ++ "/"
  let relPath := String.join parts
  base ++ "/" ++ relPath.dropRight 1 ++ ext

/-! ## Visibility

    Control what's exported from a module.
-/

/-- Visibility of a definition -/
inductive Visibility where
  | pub     : Visibility  -- Exported and visible to importers
  | priv    : Visibility  -- Only visible within the module
  deriving Repr, BEq, Inhabited

/-! ## Module Entries

    A module contains a sequence of declarations.
-/

/-- A single declaration in a module -/
inductive ModDecl where
  | importMod : Visibility → Selector → ModDecl           -- import path
  | define : Visibility → String → Expr → Expr → ModDecl  -- def name : ty := tm
  | dataDecl : Visibility → GDataDesc → ModDecl            -- data declaration
  | axiomDecl : Visibility → String → Expr → ModDecl      -- axiom name : ty
  deriving Repr

/-- A complete module -/
structure Module where
  name : Selector
  decls : List ModDecl
  deriving Repr

/-! ## Module Resolution Environment

    Tracks what names are in scope and where they came from.
-/

/-- Resolution: either a local de Bruijn index or a global name -/
inductive Resolution where
  | ix : Nat → Resolution           -- Local variable
  | globalRes : GName → Resolution     -- Global definition
  deriving Repr, BEq

/-- Info about an imported name -/
structure ImportInfo where
  name : GName
  visibility : Visibility
  fromModule : Selector
  deriving Repr

/-- Module resolution environment -/
structure ResEnv where
  /-- Local variable names (for de Bruijn) -/
  locals : List String
  /-- Global name mappings: string → name + visibility + source -/
  globals : Std.HashMap String ImportInfo
  /-- Native definitions defined in this module -/
  natives : List GName
  deriving Inhabited

/-- Empty resolution environment -/
def ResEnv.empty : ResEnv := {
  locals := []
  globals := Std.HashMap.emptyWithCapacity 100
  natives := []
}

/-- Add a local binding -/
def ResEnv.bind (x : String) (env : ResEnv) : ResEnv :=
  { env with locals := x :: env.locals }

/-- Add multiple local bindings -/
def ResEnv.bindN (xs : List String) (env : ResEnv) : ResEnv :=
  { env with locals := xs ++ env.locals }

/-- Look up a variable, returning resolution -/
def ResEnv.get (x : String) (env : ResEnv) : Option Resolution :=
  -- First check locals
  match env.locals.findIdx? (· == x) with
  | some idx => some (.ix idx)
  | none =>
    -- Then check globals
    match env.globals[x]? with
    | some info => some (.globalRes info.name)
    | none => none

/-- Add a native global definition -/
def ResEnv.addNative (vis : Visibility) (gname : GName) (env : ResEnv) : ResEnv :=
  let info : ImportInfo := { name := gname, visibility := vis, fromModule := [] }
  { env with
    globals := env.globals.insert gname.name info
    natives := gname :: env.natives }

/-- Import a global from another module -/
def ResEnv.importGlobal (vis : Visibility) (gname : GName) (fromMod : Selector) (env : ResEnv) : ResEnv :=
  let info : ImportInfo := { name := gname, visibility := vis, fromModule := fromMod }
  { env with globals := env.globals.insert gname.name info }

/-- Import all public names from another ResEnv -/
def ResEnv.importPublic (vis : Visibility) (other : ResEnv) (fromMod : Selector) (env : ResEnv) : ResEnv :=
  other.globals.fold (init := env) fun acc _s info =>
    if info.visibility == Visibility.pub then
      acc.importGlobal vis info.name fromMod
    else
      acc

/-- Get all public exports -/
def ResEnv.exports (env : ResEnv) : List GName :=
  env.globals.fold (init := []) fun acc _ info =>
    if info.visibility == Visibility.pub then info.name :: acc else acc

/-! ## Module Loading State

    Track loaded modules and their exports.
-/

/-- Cache of loaded modules -/
structure ModuleCache where
  /-- Loaded modules: selector → (ResEnv, GlobalEnv additions) -/
  modules : Std.HashMap String (ResEnv × GlobalEnv)
  /-- Loading in progress (for cycle detection) -/
  loading : List Selector

instance : Inhabited ModuleCache where
  default := { modules := Std.HashMap.emptyWithCapacity 50, loading := [] }

/-- Empty module cache -/
def ModuleCache.empty : ModuleCache := default

/-- Check if a module is already loaded -/
def ModuleCache.isLoaded (sel : Selector) (cache : ModuleCache) : Bool :=
  cache.modules.contains (selectorToPath sel)

/-- Check for cyclic dependency -/
def ModuleCache.isCyclic (sel : Selector) (cache : ModuleCache) : Bool :=
  cache.loading.contains sel

/-- Mark module as being loaded -/
def ModuleCache.startLoading (sel : Selector) (cache : ModuleCache) : ModuleCache :=
  { cache with loading := sel :: cache.loading }

/-- Store a loaded module -/
def ModuleCache.store (sel : Selector) (res : ResEnv) (env : GlobalEnv) (cache : ModuleCache) : ModuleCache :=
  { modules := cache.modules.insert (selectorToPath sel) (res, env)
    loading := cache.loading.filter (· != sel) }

/-- Retrieve a loaded module -/
def ModuleCache.getModule (sel : Selector) (cache : ModuleCache) : Option (ResEnv × GlobalEnv) :=
  cache.modules[selectorToPath sel]?

/-! ## Module Elaboration

    Process module declarations into GlobalEnv.
-/

/-- Module elaboration monad -/
abbrev ModuleM := StateT (ModuleCache × GlobalEnv) (Except String)

/-- Run module elaboration -/
def runModuleM (m : ModuleM α) : Except String (α × ModuleCache × GlobalEnv) := do
  let ((result, (cache, env))) ← m.run (ModuleCache.empty, GlobalEnv.empty)
  return (result, cache, env)

/-- Get module cache -/
def getCache : ModuleM ModuleCache := do
  let (cache, _) ← get
  return cache

/-- Modify module cache -/
def modifyCache (f : ModuleCache → ModuleCache) : ModuleM Unit := do
  let (cache, env) ← get
  set (f cache, env)

/-- Get global environment -/
def getEnv : ModuleM GlobalEnv := do
  let (_, env) ← get
  return env

/-- Modify global environment -/
def modifyEnv (f : GlobalEnv → GlobalEnv) : ModuleM Unit := do
  let (cache, env) ← get
  set (cache, f env)

/-- Process a single declaration in a module -/
def processDecl (decl : ModDecl) (resEnv : ResEnv) (localEnv : GlobalEnv)
    (loadImport : Selector → ModuleM ResEnv) : ModuleM (ResEnv × GlobalEnv) := do
  match decl with
  | .importMod vis importSel =>
    -- Recursively load imported module
    let importedRes ← loadImport importSel
    let resEnv' := ResEnv.importPublic vis importedRes importSel resEnv
    return (resEnv', localEnv)
  | .define vis name ty tm =>
    let gname := GName.named name
    let localEnv' := localEnv.define gname ty tm
    let resEnv' := resEnv.addNative vis gname
    return (resEnv', localEnv')
  | .dataDecl vis desc =>
    let localEnv' := localEnv.declareDatatype desc
    let resEnv' := resEnv.addNative vis desc.name
    return (resEnv', localEnv')
  | .axiomDecl vis name ty =>
    let gname := GName.named name
    let localEnv' := localEnv.declareParam gname ty
    let resEnv' := resEnv.addNative vis gname
    return (resEnv', localEnv')

/-- Process all declarations in a module -/
def processDecls (decls : List ModDecl) (resEnv : ResEnv) (localEnv : GlobalEnv)
    (loadImport : Selector → ModuleM ResEnv) : ModuleM (ResEnv × GlobalEnv) := do
  match decls with
  | [] => return (resEnv, localEnv)
  | d :: ds =>
    let (resEnv', localEnv') ← processDecl d resEnv localEnv loadImport
    processDecls ds resEnv' localEnv' loadImport

/-- Load a module (stub - actual file loading would be in IO) -/
partial def loadModule (sel : Selector) (readFile : Selector → Option Module) : ModuleM ResEnv := do
  let cache ← getCache
  -- Check if already loaded
  if let some (res, _) := cache.getModule sel then
    return res
  -- Check for cycle
  if cache.isCyclic sel then
    throw s!"Cyclic dependency detected: {selectorToPath sel}"
  -- Mark as loading
  modifyCache (·.startLoading sel)
  -- Read module content
  match readFile sel with
  | none => throw s!"Module not found: {selectorToPath sel}"
  | some mod =>
    -- Process declarations
    let localEnv ← getEnv
    let (resEnv, localEnv') ← processDecls mod.decls ResEnv.empty localEnv (loadModule · readFile)
    -- Store in cache
    modifyEnv fun _ => localEnv'
    modifyCache (·.store sel resEnv localEnv')
    return resEnv

/-! ## Qualified Name Resolution

    Resolve qualified names like "Prelude.Path.refl"
-/

/-- Resolve a qualified name -/
def resolveQualified (parts : List String) (env : ResEnv) (cache : ModuleCache) : Option GName :=
  match parts with
  | [] => none
  | [name] =>
    -- Unqualified: look up directly
    match env.get name with
    | some (.globalRes gname) => some gname
    | _ => none
  | moduleParts =>
    -- Qualified: extract module path and name
    let name := moduleParts.getLast!
    let modPath := moduleParts.dropLast
    match cache.getModule modPath with
    | some (modRes, _) =>
      match modRes.get name with
      | some (.globalRes gname) => some gname
      | _ => none
    | none => none

/-! ## Module Dependency Graph

    Compute build order from dependencies.
-/

/-- Extract imports from a module -/
def moduleImports (mod : Module) : List Selector :=
  mod.decls.filterMap fun decl =>
    match decl with
    | .importMod _ sel => some sel
    | _ => none

/-- Topological sort of modules for build order (simple iterative approach) -/
def topologicalSort (modules : List Module) : Except String (List Selector) := do
  -- Build dependency map
  let _deps := modules.map fun mod => (mod.name, moduleImports mod)

  -- Simple approach: no external deps, just return in declaration order
  -- (A full implementation would do proper topo sort)
  if modules.isEmpty then
    return []
  else
    return modules.map (·.name)

/-! ## Example Modules -/

/-- Example: prelude.path module -/
def preludePathModule : Module := {
  name := ["prelude", "path"]
  decls := [
    .define Visibility.pub "refl" (.univ .zero) (.lit "refl_placeholder"),
    .define Visibility.pub "sym" (.univ .zero) (.lit "sym_placeholder"),
    .define Visibility.pub "trans" (.univ .zero) (.lit "trans_placeholder")
  ]
}

/-- Example: prelude.nat module -/
def preludeNatModule : Module := {
  name := ["prelude", "nat"]
  decls := [
    .define Visibility.pub "zero" (.univ .zero) (.lit "zero_placeholder"),
    .define Visibility.pub "add" (.univ .zero) (.lit "add_placeholder"),
    .define Visibility.pub "mul" (.univ .zero) (.lit "mul_placeholder")
  ]
}

/-- Example: main module importing prelude -/
def mainModule : Module := {
  name := ["main"]
  decls := [
    .importMod Visibility.pub ["prelude", "path"],
    .importMod Visibility.pub ["prelude", "nat"],
    .define Visibility.pub "main" (.univ .zero) (.lit "main_placeholder")
  ]
}

end Lego.Cubical.Module
