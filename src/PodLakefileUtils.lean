import Lake

/-!
This file provides utilities for lakefiles.
Its code is intended to be parsed and elaborated inside lakefiles using metaprogramming.

```lean4
import Lean.Elab.Import

run_cmd
  let pos ← Lean.getRefPos
  let infoState ← Lean.Elab.MonadInfoTree.getInfoState
  let scopes ← Lean.Elab.Command.getScopes
  modify fun s ↦ { s with scopes := [{ header := "" }]}
  let rec clearSourceInfo : Lean.Syntax → Lean.Syntax :=
    flip Lean.Syntax.modifyArgs (Array.map clearSourceInfo) ∘ Lean.Syntax.setInfo (.synthetic pos pos)
  let fileName := "PodLakefileUtils.lean"
  let ictx := Lean.Parser.mkInputContext (← IO.FS.readFile <| ← IO.FS.realPath s!"{defaultPackagesDir}/{pod.dirName}/src/{fileName}") fileName
  let mut (header, mpst, msgs) ← Lean.Parser.parseHeader ictx
  try
    if msgs.hasErrors then throwError "[{fileName}] Failed to parse header."
    let envModules := (← Lean.getEnv).header.modules
    for imprt in Lean.Elab.headerToImports header do
      unless envModules.any (fun m ↦ m.module == imprt.module && m.importAll || m.toImport == imprt) do
        throwError "{fileName} contains unavailable import: {imprt}"
    for _ in 0...1000 do -- Avoid spawning infinite loop zombies in case of errors
      let (stx, mpst', msgs') := Lean.Parser.parseCommand ictx {env := ← Lean.getEnv, options := {}} mpst msgs
      (mpst, msgs) := (mpst', msgs')
      if msgs'.hasErrors then throwError "[{fileName}] Failed to parse command."
      if Lean.Parser.isTerminalCommand stx then break
      Lean.Elab.Command.elabCommand (clearSourceInfo stx)
  finally
    modify fun s => { s with messages := s.messages ++ msgs, scopes, infoState }
```
-/

namespace PodLakefileUtils

set_option autoImplicit false

variable {m} [Monad m] [Lake.MonadError m] [MonadLiftT IO m] [MonadReaderOf Lake.CurrPackage m]

def parseCliArgs (s : String) : Array String :=
  Id.run <| do
    let mut (acc, cur, quoted, escaped) := (#[], "", false, false)
    for c in s do
      match c with
      | ' ' =>
        if quoted || escaped
          then
            cur := cur.push ' '
            escaped := false
          else
            if !cur.isEmpty then
              acc := acc.push cur
              cur := ""
      | '\\' =>
        if escaped then cur := cur.push '\\'
        escaped := !escaped
      | '\"' =>
        if escaped
          then
            cur := cur.push '\"'
            escaped := false
          else
            quoted := !quoted
            unless cur.isEmpty do
              acc := acc.push cur
              cur := ""
      | 'n' =>
        cur := cur.push (cond escaped '\n' 'n')
        escaped := false
      | c =>
        escaped := false
        cur := cur.push c
    if !cur.isEmpty then
      acc := acc.push cur
    return acc

structure tryRunProcess.Params where
  cmd : String
  quiet : Bool := false
  args : Array String := #[]
  cwd : Option System.FilePath := none
  env : Array (String × Option String) := #[]
  inheritEnv : Bool := true
  setsid : Bool := false

attribute [inherit_doc IO.Process.SpawnArgs.cmd] tryRunProcess.Params.cmd
attribute [inherit_doc IO.Process.SpawnArgs.args] tryRunProcess.Params.args
attribute [inherit_doc IO.Process.SpawnArgs.cwd] tryRunProcess.Params.cwd
attribute [inherit_doc IO.Process.SpawnArgs.env] tryRunProcess.Params.env
attribute [inherit_doc IO.Process.SpawnArgs.inheritEnv] tryRunProcess.Params.inheritEnv
attribute [inherit_doc IO.Process.SpawnArgs.setsid] tryRunProcess.Params.setsid

def tryRunProcess.command (ps : tryRunProcess.Params) : IO String := do
  let command := ps.args.foldl (fun s x ↦ s ++ " " ++ (if x.contains ' ' then s!"\"{x.replace "\"" "\\\""}\"" else x)) ps.cmd
  let currentDir ← IO.currentDir
  let processDir ← IO.FS.realPath <| match ps.cwd with | none => "." | some wd => wd.toString
  let processDir := processDir.toString.replace currentDir.toString "./"
  unless ps.quiet do
    let stdout ← IO.getStdout
    stdout.putStrLn <|
      if ← stdout.isTty then
        Lake.Ansi.chalk "36" (" [" ++ processDir ++ "]$ ") ++ command
      else
        s!"[{processDir}]$ {command}"
  pure command

def tryRunProcess.waitCheckExitCode {stdioConfig} (command : String) (process : IO.Process.Child stdioConfig) : IO Unit := do
  let exitCode ← process.wait
  if exitCode ≠ 0 then
    Lake.error s!"external command returned non-zero exit status {exitCode}: {command}"

def tryRunProcessGetStdout (ps : tryRunProcess.Params) : IO String := do
  let command ← tryRunProcess.command ps
  let process ← IO.Process.spawn { ps with stdout := .piped, stderr := .inherit, stdin := .null }
  let stdout ← IO.asTask process.stdout.readToEnd Task.Priority.dedicated
  tryRunProcess.waitCheckExitCode command process
  return ← IO.ofExcept stdout.get

def tryRunProcessGetStderr (ps : tryRunProcess.Params) : IO String := do
  let command ← tryRunProcess.command ps
  let process ← IO.Process.spawn { ps with
    stdout := cond ps.quiet .null .inherit
    stderr := .piped
    stdin := .null
  }
  let stderr ← IO.asTask process.stderr.readToEnd Task.Priority.dedicated
  tryRunProcess.waitCheckExitCode command process
  return ← IO.ofExcept stderr.get

def tryRunProcess (ps : tryRunProcess.Params) : IO Unit := do
  let command ← tryRunProcess.command ps
  let process ← IO.Process.spawn { ps with
    toStdioConfig :=
      if ps.quiet
        then { stdout := .null, stderr := .inherit, stdin := .null }
        else { stdout := .inherit, stderr := .inherit, stdin := .null }
  }
  tryRunProcess.waitCheckExitCode command process

def buildDir : m System.FilePath :=
  Lake.getCurrPackage? >>= fun
  | some p => pure p.buildDir
  | none => Lake.error "no current package available"

structure downloadGit.Params where
  /-- Git binary to execute. -/
  git : String := "git"
  quiet : Bool := false
  url : String
  commit : String
  /-- Preferably under `.lake/build` so that it will be cleaned by `lake clean`. -/
  directory : System.FilePath
  /-- Repository directory name. The path will be `{params.directory}/{params.name}`. -/
  name : String
  cwd : Option System.FilePath := none
  env : Array (String × Option String) := #[]
  inheritEnv : Bool := true
  setsid : Bool := false

attribute [inherit_doc IO.Process.SpawnArgs.cwd] downloadGit.Params.cwd
attribute [inherit_doc IO.Process.SpawnArgs.env] downloadGit.Params.env
attribute [inherit_doc IO.Process.SpawnArgs.inheritEnv] downloadGit.Params.inheritEnv
attribute [inherit_doc IO.Process.SpawnArgs.setsid] downloadGit.Params.setsid

/--
Ensures `{params.directory}/{params.name}` contains a vaild git repository with the specified commit.
Returns repository path.
-/
def downloadGit  (ps : downloadGit.Params) : IO System.FilePath := do
  IO.FS.createDirAll ps.directory
  let repoDir := ps.directory / ps.name
  repeat
    let gitCdup ←
      try
        tryRunProcessGetStdout { ps with
          cmd := ps.git
          args := #["-C", repoDir.toString, "rev-parse", "--show-cdup"]
        }
      catch _ =>
        break
    unless gitCdup.trimAsciiEnd.isEmpty do break
    let gitOrigin ← tryRunProcessGetStdout { ps with
      cmd := ps.git
      args := #["-C", repoDir.toString, "remote", "get-url", "origin"]
    }
    unless gitOrigin.trimAsciiEnd == ps.url do break
    let gitCommit ← tryRunProcessGetStdout { ps with
      cmd := ps.git
      args := #["-C", repoDir.toString, "rev-parse", "--verify", "HEAD"]
    }
    unless gitCommit.trimAsciiEnd == ps.commit do break
    try
      let args := #["-C", repoDir.toString, "diff-index", "HEAD", "--"]
      let args := if ps.quiet then args.insertIdx! 3 "--quiet" else args
      tryRunProcess { ps with cmd := ps.git, args }
    catch _ =>
      tryRunProcess { ps with
        cmd := ps.git
        args := #["-C", repoDir.toString, "reset", "--hard", "HEAD"]
      }
    let gitUntracked ← tryRunProcessGetStdout { ps with
      cmd := ps.git
      args := #[
        "-C", repoDir.toString, "ls-files", "--exclude-standard", "--others", "--deduplicate", "--full-name"
      ]
    }
    for file in gitUntracked.lines do
      IO.FS.removeFile <| repoDir / file.toString
    return repoDir
  if !ps.quiet then
    println! "Removing {repoDir}"
  try IO.FS.removeDirAll repoDir catch _ => pure ()
  tryRunProcess { ps with
    cmd := ps.git
    args := #["clone", "--revision=" ++ ps.commit, "--depth=1", ps.url, repoDir.toString]
  }
  return repoDir

structure cmakeGenerate.Params where
  /-- CMake binary to execute. -/
  cmake : String := "cmake"
  quiet : Bool := false
  settings : Array (String × String) := #[]
  source : Option String := none
  output : Option String := none
  generator : Option String := none
  extraArgs : Array String := #[]
  cwd : Option System.FilePath := none
  env : Array (String × Option String) := #[]
  inheritEnv : Bool := true
  setsid : Bool := false

attribute [inherit_doc IO.Process.SpawnArgs.cwd] cmakeGenerate.Params.cwd
attribute [inherit_doc IO.Process.SpawnArgs.env] cmakeGenerate.Params.env
attribute [inherit_doc IO.Process.SpawnArgs.inheritEnv] cmakeGenerate.Params.inheritEnv
attribute [inherit_doc IO.Process.SpawnArgs.setsid] cmakeGenerate.Params.setsid

def cmakeGenerate (ps : cmakeGenerate.Params) : IO Unit := do
  let mut args := ps.settings.map fun (k, v) => s!"-D{k}={v}"
  if let some source := ps.source then
    args := args.push "-S" |>.push source
  if let some output := ps.output then
    args := args.push "-B" |>.push output
  if let some generator := ps.generator then
    args := args.push "-G" |>.push generator
  tryRunProcess { ps with cmd := ps.cmake, args := args ++ ps.extraArgs }

structure cmakeBuild.Params where
  /-- CMake binary to execute. -/
  cmake : String := "cmake"
  quiet : Bool := false
  directory : String
  /-- Empty means default target. -/
  targets : Array String := #[]
  extraArgs : Array String := #[]
  buildToolArgs : Array String := #[]
  cwd : Option System.FilePath := none
  env : Array (String × Option String) := #[]
  inheritEnv : Bool := true
  setsid : Bool := false

attribute [inherit_doc IO.Process.SpawnArgs.cwd] cmakeBuild.Params.cwd
attribute [inherit_doc IO.Process.SpawnArgs.env] cmakeBuild.Params.env
attribute [inherit_doc IO.Process.SpawnArgs.inheritEnv] cmakeBuild.Params.inheritEnv
attribute [inherit_doc IO.Process.SpawnArgs.setsid] cmakeBuild.Params.setsid

def cmakeBuild (ps : cmakeBuild.Params) : IO Unit := do
  let mut args := #["--build", ps.directory]
  unless ps.targets.isEmpty do
    args := ps.targets.foldl (·.push) (args.push "--target")
  args := args ++ ps.extraArgs
  unless ps.buildToolArgs.isEmpty do
    args := args.push "--" |>.append ps.buildToolArgs
  tryRunProcess { ps with cmd := ps.cmake, args }

inductive getClangIncludeDirs.Language where
| c
| cpp

structure getClangIncludeDirs.Params where
  /-- clang binary to execute. -/
  clang : String := "clang"
  quiet : Bool := false
  language : getClangIncludeDirs.Language := .c

def getClangCppIncludeDirs (ps : getClangIncludeDirs.Params) : IO (Array String.Slice) := do
  let clangOutput ←
    IO.FS.withTempFile fun _ emptyFile =>
      PodLakefileUtils.tryRunProcessGetStderr {
        cmd := ps.clang,
        quiet := ps.quiet,
        args := #[
          "-E",
          "-v",
          "-x",
          match ps.language with | .c => "c" | .cpp => "c++",
          emptyFile.toString,
        ]
      }
  let mut lineIt := clangOutput.lines
  repeat
    match lineIt.step with
    | .yield it line _ =>
      lineIt := it
      if line.contains "#include <...> search starts here:" then
        break
    | .skip it _ =>
      lineIt := it
    | .done _ =>
      return #[]
  let mut paths := #[]
  repeat
    match lineIt.step with
    | .yield it line _ => (lineIt, paths) := (it, paths.push line.trimAscii)
    | .skip it _ => lineIt := it
    | .done _ => break
  return paths

structure getClangLibcppIncludeDir.params where
  /-- clang binary to execute. -/
  clang : String := "clang"
  quiet : Bool := false

def getClangLibcppIncludeDir (ps : getClangLibcppIncludeDir.params) : IO System.FilePath := do
  let candidates ← getClangCppIncludeDirs { ps with language := .cpp }
  for candidate in candidates do
    let includeDir := System.FilePath.mk candidate.toString / "c++" / "v1"
    if ← (includeDir / "cstddef").pathExists then
      return includeDir
  Lake.error "could not find libc++ include path"

end PodLakefileUtils
