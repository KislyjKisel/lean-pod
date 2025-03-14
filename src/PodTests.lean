import LSpec
import Pod

open LSpec

namespace Pod.Tests

def float32 := group "Float32"
  <| test "Substring.toFloat32? 1.24" (Pod.Substring.toFloat32? "1.24".toSubstring == some 1.24)
  <| test "Substring.toFloat32? -0.1" (Pod.Substring.toFloat32? "-0.1".toSubstring == some (-0.1))
  <| test "Substring.toFloat32? 1.4x" (Pod.Substring.toFloat32? "1.4x".toSubstring == none)
  <| test "toLittleEndian toBits bswap = toBits toBigEndian"
    ((Pod.Float32.toLittleEndian (3.14 : Float32)).toBits.bswap == (3.14 : Float32).toBits.toBigEndian)
  <| test "isNormal 1" (Pod.Float32.isNormal 1)
  <| test "¬ isNormal 0" (Pod.Float32.isNormal 0).not
  <| test "¬ isNormal ∞" (Pod.Float32.isNormal Pod.Float32.inf).not

instance : Repr ByteArray where
  reprPrec x _ := "#" ++ repr x.data

instance : BEq ByteArray where
  beq x y := x.data == y.data

def bytesView :=
  let ba1 := ByteArray.mk #[1, 2, 3, 4, 5]
  group "BytesView"
  <| test "view toByteArray" (ba1 == ba1.view.toByteArray)
  <| test "getElem = view drop take get" (ba1[1] == (ba1.view.drop 1 (by decide) |>.take 1 (by decide) |>.get))

def bytesRef :=
  let ba1 := ByteArray.mk #[1, 2, 3, 4, 5]
  group "BytesRef"
  <| test "set = withRef setOffElUnal" (
      let i : Fin ba1.size := ⟨4, by decide⟩
      let y : UInt8 := 42
      (ba1.set i y) == (Prod.snd <| runST <| λ _ ↦ ba1.withRef λ br ↦ br.setOffElUnal i.val y i.isLt)
  )
  <| test "getElem = view asRef drop take get" (
      let i : Fin ba1.size := ⟨2, by decide⟩
      ba1[i] == (
        runST λ _ ↦
          ba1.view.asRef λ br ↦
            Nat.gcd_one_left _ ▸ br.drop i (Nat.le_of_lt i.isLt) |>.take 1 (by decide) |>.get
      )
  )

def deque :=
  group "Deque"
  <| test "size empty = 0" ((Deque.empty : Deque Nat).size == 0)
  <| test "size (singleton 42) = 1" ((Deque.singleton 42).size == 1)
  <| test "size (mkEmpty 100) = 0" ((Deque.mkEmpty 100 : Deque Nat).size == 0)
  <| test "size (empty.pushBack 42) = 1" ((Deque.empty.pushBack 42).size == 1)
  <| test "size ((empty.pushFront 42).pushFront 12) = 2" ((Deque.empty.pushFront 42 |>.pushFront 12).size == 2)
  <| test "isEmpty empty" (Deque.empty : Deque Nat).isEmpty
  <| test "isEmpty (ofList [])" (Deque.ofList [] : Deque Nat).isEmpty
  <| test "isEmpty (ofArray #[])" (Deque.ofArray #[] : Deque Nat).isEmpty
  <| test "¬ isEmpty (empty.pushBack true)" (Deque.empty.pushBack true).isEmpty.not
  <| test "¬ isEmpty (ofList [1])" (Deque.ofList [1]).isEmpty.not
  <| test "toArray∘ofArray [true]" ((Deque.ofArray #[true]).toArray == #[true])
  <| test "toList∘ofList ['x']" ((Deque.ofList ['x']).toList == ['x'])
  <| test "toArray∘ofList [1,2,3]" ((Deque.ofList [1, 2, 3]).toArray == #[1, 2, 3])
  <| test "toArray∘ofList []" ((Deque.ofList ([] : List Nat)).toArray == #[])
  <| test "toList∘ofArray ['a','b','c']" ((Deque.ofArray #["a", "b", "c"]).toList == ["a", "b", "c"])
  <| test "toList∘ofArray #[]" ((Deque.ofArray (#[] : Array Nat)).toList == [])
  <| test "(replicate 5 'w').toArray = Array.mkArray 5 'w'"
    ((Deque.replicate 5 'w').toArray == (Array.mkArray 5 'w'))
  <| test "(empty.pushBack 1).peekBack _ = 1"
    ((if h: _ then (Deque.empty.pushBack 1).peekBack h else 0) == 1)
  <| test "(empty.pushFront 'x' |>.pushBack 'y').peekFront _ = 'x'"
    ((if h: _ then (Deque.empty.pushFront 'x' |>.pushBack 'y').peekFront h else '#')  == 'x')
  <| test "(empty.pushFront 'y' |>.pushBack 'z' |>.pushFront 'x').toList = ['x','y','z']"
    ((Deque.empty.pushFront 'y' |>.pushBack 'z' |>.pushFront 'x').toList == ['x','y','z'])
  <| test "(ofList ['x','y','z'] |>.get! 1) = 'y'"
    ((Deque.ofList ['x','y','z'] |>.get! 1) == 'y')

def fixnumSlotMap :=
  let empty := FixnumSlotMap.empty (α := Nat) 15 16
  let (k1, m1) := empty.insert 1
  let (k2, m12) := m1.insert 2
  let (k3, m123) := m12.insert 3
  let m13 := m123.erase k2
  group "FixnumSlotMap"
  <| test "{ } ¬ isValid 1" (empty.isValid k1).not
  <| test "{ 1 } isValid 1" (m1.isValid k1)
  <| test "{ 1, 2 } ¬ isValid top" (m12.isValid m12.top).not
  <| test "{ 1 } firstValid = 1" (m1.firstValid.map Subtype.val == some k1)
  <| test "{ 1, 2, 3 } nextValid 1 = 2" ((m123.nextValid k1 |>.map Subtype.val) == some k2)
  <| test "{ 1, 2, 3 } nextValid 2 = 3" ((m123.nextValid k2 |>.map Subtype.val) == some k3)
  <| test "{ 1, 2, 3 } nextValid 3 = none" (m123.nextValid k3 == none)
  <| test "{ 1, 2 } top = 3" (m12.top == k3)
  <| test "{ 1, 2, 3 } \\ 2 |>.get? 1" (m12.get? k1 = some 1)
  <| test "{ 1, 2, 3 } \\ 2 |>.get? 2" (m13.get? k2 = none)
  <| test "{ 1, 2, 3 } \\ 2 |>.get? 3" (m13.get? k3 = some 3)
  <| test "{ 1, 2, 3 } \\ 2 |>.get? x" (m13.get? 14 = none)
  <| test "{ 1, 2, 3 } |>.set 2 |>.get 2" ((m123.setD k2 4).get? k2 = some 4)
  <| test "{ 1, 2, 3 } \\ 2 |>.set 2 |>.get 2" ((m13.setD k2 4).get? k2 = none)

end Pod.Tests

def main : List String → IO UInt32 :=
  lspecIO ∘ Std.HashMap.ofList ∘ List.map (Prod.map id List.singleton) <| [
    ("float32", Pod.Tests.float32),
    ("bytesView", Pod.Tests.bytesView),
    ("bytesRef", Pod.Tests.bytesRef),
    ("deque", Pod.Tests.deque),
    ("fixnumSlotMap", Pod.Tests.fixnumSlotMap),
  ]
