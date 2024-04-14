-- size of the buffer in bytes
def bufsize : USize := 20 * 1024

/-- copy the contents of `stream` into stdout -/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

/-- open and return a stream with the given filename; returning `none` if the
file can't be opened for reading -/
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"file not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

/--
dump the contents of files named by `args` into standard output; the special
name "-" indicates standard input
-/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode

  | "-"::args =>
    let stream ← IO.getStdin
    dump stream
    process exitCode args

  | filename::args =>
    let stream ← fileStream filename
    match stream with
    | none =>
      process 1 args

    | some stream =>
      dump stream
      process exitCode args

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => process 0 ["-"]
  | _  => process 0 args



