import Pod.BytesView

def main : IO Unit := do
  let bb := (ByteArray.mk #[1, 2, 3, 4, 5]).view
  IO.println $ bb[0]!
  IO.println $ bb[1]!
  IO.println $ bb[2]!
  IO.println $ bb[3]!
  IO.println $ bb[4]!

  let mut count := 10
  repeat do
    IO.println "HI"
    IO.sleep 100
    count := count - 1
    if count = 0 then break
