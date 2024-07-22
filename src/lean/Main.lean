import Pod

def test : ByteArray :=
  let a := #[142, 142, 142, 142, 142]
  (ByteArray.mk a).withRef λ ref ↦ do
    let mut i : Nat := 0
    while h: i < 5 do
      Pod.BytesRef.setOffEl (Eq.ndrec (motive := Pod.BytesRefMut _ _) ref (by rfl)) i i.toUInt8 $ by
        show i * 1 + 1 ≤ 5
        rewrite [Nat.mul_one]
        apply Nat.succ_le_of_lt
        exact h
      i := i + 1

/-- Wraps `onFinalize` in IO to avoid it getting marked as persistent. -/
def makeOnFinalize (s : String) : IO Pod.OnFinalize :=
  pure (Pod.onFinalize <| (IO.println s).catchExceptions λ _ ↦ pure ())

def onFinalizeMutCb (s : String) : BaseIO Unit :=
  (IO.println s).catchExceptions λ _ ↦ pure ()

def fixnumSlotMapForEach {α iW gW} [Nonempty α] (m : Pod.FixnumSlotMap iW gW α) (f : α → IO Unit) : IO Unit := do
  if let some k0 := m.firstValid
    then do
      f (m.get k0.1 k0.2)
      let mut k := k0.1
      repeat
        let k' := m.nextValid k
        if let some k' := k'
          then
            f (m.get k'.1 k'.2)
            k := k'.1
          else
            break
    else pure ()

def testFixnumSlotMap : IO Unit := do
  let map := Pod.FixnumSlotMap.empty (α := Nat) 22 9
  let (_, map) := map.insert 1
  let (k2, map) := map.insert 2
  let (_, map) := map.insert 3
  let map := map.erase k2
  let (_, map) := map.insert 4
  fixnumSlotMapForEach map λ x ↦ IO.println x

def main : IO Unit := do
  let ofImm1 ← makeOnFinalize "OnFinalize 1"
  let ofImm2 ← makeOnFinalize "OnFinalize 2"
  let ofMut1 ← Pod.onFinalizeMut <| onFinalizeMutCb "OnFinalizeMut 1 (unset)"
  let ofMut2 ← Pod.onFinalizeMut <| onFinalizeMutCb "OnFinalizeMut 2 (unsuppressed)"
  let bb := test.view
  IO.println $ bb[0]!
  IO.println $ bb[1]!
  IO.println $ bb[2]!
  IO.println $ bb[3]!
  IO.println $ bb[4]!

  IO.println $ "\"3.14d\" toFloat32 " ++ toString "3.14d".toFloat32?
  IO.println $ "\"3.14\" toFloat32 " ++ toString "3.14".toFloat32?
  IO.println $ "&\"3.14d\" toFloat32 " ++ toString "3.14d".toSubstring.toFloat32?
  IO.println $ "&\"3.14\" toFloat32 " ++ toString "3.14".toSubstring.toFloat32?

  let uv : Pod.UVector UInt64 3 := .replicate 42
  IO.print s!"UV: {uv[0]}, {uv[1]}, {uv[2]!} --> "
  let uv := ((uv.set! 2 (UInt64.complement 0)).set 0 0).set 1 ((UInt64.complement 0) / 3)
  IO.println s!"{uv[0]}, {uv[1]!}, {uv[2]}"

  testFixnumSlotMap

  ofMut2.suppress
  let mut count := 10
  repeat do
    IO.println "HI"
    IO.sleep 100
    count := count - 1
    if count = 0 then break
  ofMut1.set (onFinalizeMutCb "OnFinalizeMut 1 (set)")
  Pod.touch ofImm2 (pure ())
