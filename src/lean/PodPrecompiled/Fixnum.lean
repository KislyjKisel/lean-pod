import PodPrecompiled.Meta
import PodPrecompiled.Storable
import PodPrecompiled.UInt

namespace Pod

def UFixnum.bitWidth := (System.Platform.numBits - 1)

abbrev UFixnum.size : Nat := (2 ^ UFixnum.bitWidth) - 1 + 1

theorem UFixnum.size_eq : Or (UFixnum.size = 2147483648) (UFixnum.size = 9223372036854775808) :=
  show Or ((Nat.succ (Nat.sub (2 ^ (System.Platform.numBits - 1)) 1)) = 2147483648) (Eq (Nat.succ (Nat.sub (2 ^ (System.Platform.numBits - 1)) 1)) 9223372036854775808) from
  match System.Platform.numBits, System.Platform.numBits_eq with
  | _, Or.inl rfl => Or.inl (by decide)
  | _, Or.inr rfl => Or.inr (by decide)

theorem UFixnum.size_ge : UFixnum.size ≥ 2147483648 :=
  match UFixnum.size_eq with
  | .inl h => Nat.le_of_eq h.symm
  | .inr h => Nat.le_trans (by decide) (Nat.le_of_eq h.symm)

theorem UFixnum.bitWidth_ge : UFixnum.bitWidth ≥ 31 := by
  unfold bitWidth
  cases System.Platform.numBits_eq
  case inl h => rewrite [h]; decide
  case inr h => rewrite [h]; decide

/--
A `UFixnum` is the largest unsigned integer type stored unboxed.

For example, if running on a 32-bit machine, UFixnum is equivalent to UInt31.
Or on a 64-bit machine, UInt63.
-/
structure UFixnum where
  val : Fin UFixnum.size
deriving Repr, Inhabited, DecidableEq

def UFixnum.maximum : UFixnum :=
  ⟨(2 ^ bitWidth - 1), Nat.lt_succ_self _⟩

def UFixnum.ofNatCore (x : Nat) (h : x < size) : UFixnum :=
  ⟨x, h⟩

def UFixnum.ofNatCore' (x : Nat) (h : x < 2147483648) : UFixnum :=
  ⟨x, Nat.lt_of_lt_of_le h size_ge⟩

private unsafe
def UFixnum.ofNatImpl (x : Nat) : UFixnum :=
  ⟨(x &&& ((1 <<< (System.Platform.numBits - 1)) - 1)), lcProof⟩

@[implemented_by ofNatImpl]
def UFixnum.ofNat (x : Nat) : UFixnum :=
  .mk $ Fin.ofNat' x (Nat.lt_of_lt_of_le (by decide) size_ge)

instance UFixnum.instOfNat {n} : OfNat UFixnum n := ⟨.ofNat n⟩

@[extern c inline "lean_box(#1)"]
def UFixnum.ofBool (x : Bool) : UFixnum :=
  cond x 1 0

def UFixnum.ofUInt8 (x : UInt8) : UFixnum :=
  ⟨x.toNat, Nat.lt_trans x.val.isLt $ Nat.lt_of_lt_of_le (by decide) size_ge⟩

def UFixnum.ofUInt16 (x : UInt16) : UFixnum :=
  ⟨x.toNat, Nat.lt_trans x.val.isLt $ Nat.lt_of_lt_of_le (by decide) size_ge⟩

@[extern c inline "lean_box(#1 & (((size_t)1 << ((sizeof(size_t) * 8) - 1)) - 1))"]
opaque UFixnum.ofUInt32 (x : UInt32) : UFixnum

@[extern c inline "lean_box(#1 & (((size_t)1 << ((sizeof(size_t) * 8) - 1)) - 1))"]
opaque UFixnum.ofUInt64 (x : UInt64) : UFixnum

@[inline]
def UFixnum.toNat (x : UFixnum) : Nat :=
  x.val.val

theorem UFixnum.toNat_lt (x : UFixnum) : x.toNat < 9223372036854775808 :=
  match UFixnum.size_eq with
  | .inl h => Nat.lt_trans x.val.isLt (by rewrite [h]; decide)
  | .inr h => h ▸ x.val.isLt

@[extern c inline "((size_t)#1 >> 1) != 0"]
def UFixnum.toBool (x : UFixnum) : Bool :=
  x.toNat != 0

@[extern c inline "lean_unbox(#1)"]
opaque UFixnum.toUInt8 (x : UFixnum) : UInt8

@[extern c inline "lean_unbox(#1)"]
opaque UFixnum.toUInt16 (x : UFixnum) : UInt16

@[extern c inline "lean_unbox(#1)"]
def UFixnum.toUInt32 (x : UFixnum) : UInt32 :=
  x.toNat.toUInt32

@[extern c inline "lean_unbox(#1)"]
def UFixnum.toUInt64 (x : UFixnum) : UInt64 :=
  UInt64.ofNatCore x.toNat (Nat.lt_trans (toNat_lt x) (by decide))

@[extern c inline "#1 == #2"]
def UFixnum.beq (x y : UFixnum) : Bool :=
  x.toNat == y.toNat

@[extern c inline "(size_t)#1 < (size_t)#2"]
def UFixnum.blt (x y : UFixnum) : Bool :=
  x.toNat < y.toNat

@[extern c inline "(size_t)#1 <= (size_t)#2"]
def UFixnum.ble (x y : UFixnum) : Bool :=
  x.toNat <= y.toNat

@[extern c inline "(void*)(((size_t)#1 ^ (size_t)#2) | 1)"]
def UFixnum.xor (x y : UFixnum) : UFixnum :=
  .mk <| x.val.xor y.val

@[extern c inline "(void*)((size_t)#1 | (size_t)#2)"]
def UFixnum.lor (x y : UFixnum) : UFixnum :=
  .mk <| x.val.lor y.val

@[extern c inline "(void*)((size_t)#1 & (size_t)#2)"]
def UFixnum.land (x y : UFixnum) : UFixnum :=
  .mk <| x.val.land y.val

@[extern c inline "(void*)(~(size_t)#1)"]
opaque UFixnum.complement (x : UFixnum) : UFixnum

@[extern c inline "lean_box(lean_unbox(#1) << (lean_unbox(#2) % (sizeof(size_t) * 8)))"]
opaque UFixnum.shiftLeft (x y : UFixnum) : UFixnum

@[extern c inline "lean_box(lean_unbox(#1) >> (lean_unbox(#2) % (sizeof(size_t) * 8)))"]
opaque UFixnum.shiftRight (x y : UFixnum) : UFixnum

@[extern c inline "lean_box(lean_unbox(#1) + lean_unbox(#2))"]
def UFixnum.add (x y : UFixnum) : UFixnum :=
  .mk <| x.val + y.val

@[extern c inline "lean_box(lean_unbox(#1) - lean_unbox(#2))"]
def UFixnum.sub (x y : UFixnum) : UFixnum :=
  .mk <| x.val - y.val

@[extern c inline "lean_box(lean_unbox(#1) * lean_unbox(#2))"]
def UFixnum.mul (x y : UFixnum) : UFixnum :=
  .mk <| x.val * y.val

@[extern c inline "(lean_unbox(#2) == 0) ? lean_box(0) : (lean_box(lean_unbox(#1) / lean_unbox(#2)))"]
def UFixnum.div (x y : UFixnum) : UFixnum :=
  .mk <| x.val / y.val

@[extern c inline "(lean_unbox(#2) == 0) ? #1 : (lean_box(lean_unbox(#1) % lean_unbox(#2)))"]
def UFixnum.mod (x y : UFixnum) : UFixnum :=
  .mk <| x.val % y.val

instance : BEq UFixnum := ⟨UFixnum.beq⟩
instance : Xor UFixnum := ⟨UFixnum.xor⟩
instance : OrOp UFixnum := ⟨UFixnum.lor⟩
instance : AndOp UFixnum := ⟨UFixnum.land⟩
instance : Complement UFixnum := ⟨UFixnum.complement⟩
instance : ShiftLeft UFixnum := ⟨UFixnum.shiftLeft⟩
instance : ShiftRight UFixnum := ⟨UFixnum.shiftRight⟩
instance : Add UFixnum := ⟨UFixnum.add⟩
instance : Sub UFixnum := ⟨UFixnum.sub⟩
instance : Mul UFixnum := ⟨UFixnum.mul⟩
instance : Div UFixnum := ⟨UFixnum.div⟩
instance : Mod UFixnum := ⟨UFixnum.mod⟩

instance : ToString UFixnum where
  toString x := toString x.toNat

instance : Storable UFixnum where
  byteSize := byteSize USize
  alignment := alignment USize
  alignment_dvd_byteSize := alignment_dvd_byteSize
  byteSize_gt_zero := byteSize_gt_zero
