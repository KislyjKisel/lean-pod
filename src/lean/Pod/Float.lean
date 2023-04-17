/-! # Float32 -/

namespace Pod

structure Float32 where
  bits : UInt32
deriving Inhabited

namespace Float32

/-! # Transparent Float32 constants -/

def zero : Float32 := .mk 0x00000000
def negZero : Float32 := .mk 0x80000000
def one : Float32 := .mk 0x3F800000
def negOne : Float32 := .mk 0xBF800000
def two : Float32 := .mk 0x40000000
def negTwo : Float32 := .mk 0xC0000000
def half : Float32 := .mk 0x3F000000
def negHalf : Float32 := .mk 0xBF000000
def inf : Float32 := .mk 0x7F800000
def negInf : Float32 := .mk 0xFF800000
def pi : Float32 := .mk 0x40490FDB

end Float32

end Pod

@[extern "lean_pod_Float_toFloat32"]
opaque Float.toFloat32 : Float → Pod.Float32

@[extern "lean_pod_UInt8_toFloat32"]
opaque UInt8.toFloat32 : UInt8 → Pod.Float32

@[extern "lean_pod_UInt16_toFloat32"]
opaque UInt16.toFloat32 : UInt16 → Pod.Float32

@[extern "lean_pod_UInt32_toFloat32"]
opaque UInt32.toFloat32 : UInt32 → Pod.Float32

@[extern "lean_pod_UInt64_toFloat32"]
opaque UInt64.toFloat32 : UInt64 → Pod.Float32

@[extern "lean_pod_USize_toFloat32"]
opaque USize.toFloat32 : USize → Pod.Float32

namespace Pod.Float32

@[extern "lean_pod_Float32_toString"]
opaque toString : Float32 → String

@[extern "lean_pod_Float32_toFloat"]
opaque toFloat : Float32 → Float

@[extern "lean_pod_Float32_toUInt8"]
opaque toUInt8 : Float32 → UInt8

@[extern "lean_pod_Float32_toUInt16"]
opaque toUInt16 : Float32 → UInt16

@[extern "lean_pod_Float32_toUInt32"]
opaque toUInt32 : Float32 → UInt32

@[extern "lean_pod_Float32_toUInt64"]
opaque toUInt64 : Float32 → UInt64

@[extern "lean_pod_Float32_toUSize"]
opaque toUSize : Float32 → USize

@[extern "lean_pod_Float32_add"]
opaque add : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_sub"]
opaque sub : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_mul"]
opaque mul : Float32 → Float32 → Float32

@[inline]
def sqr (value : Float32) : Float32 := value.mul value

@[extern "lean_pod_Float32_div"]
opaque div : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_neg"]
opaque neg : Float32 → Float32

@[extern "lean_pod_Float32_beq"]
opaque beq : Float32 → Float32 → Bool

@[extern "lean_pod_Float32_blt"]
opaque blt : Float32 → Float32 → Bool

@[extern "lean_pod_Float32_ble"]
opaque ble : Float32 → Float32 → Bool

@[extern "lean_pod_Float32_min"]
opaque min : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_max"]
opaque max : Float32 → Float32 → Float32 

@[extern "lean_pod_Float32_isNaN"]
opaque isNaN : Float32 → Bool

@[extern "lean_pod_Float32_isFinite"]
opaque isFinite : Float32 → Bool

@[extern "lean_pod_Float32_isInf"]
opaque isInf : Float32 → Bool

@[extern "lean_pod_Float32_isNormal"]
opaque isNormal : Float32 → Bool

@[extern "lean_pod_Float32_isUnordered"]
opaque isUnordered : Float32 → Float32 → Bool

@[extern "lean_pod_Float32_frExp"]
opaque frExp : Float32 → Float32 × Int

@[extern "lean_pod_Float32_sin"]
opaque sin : Float32 → Float32

@[extern "lean_pod_Float32_cos"]
opaque cos : Float32 → Float32

@[extern "lean_pod_Float32_tan"]
opaque tan : Float32 → Float32

@[extern "lean_pod_Float32_asin"]
opaque asin : Float32 → Float32

@[extern "lean_pod_Float32_acos"]
opaque acos : Float32 → Float32

@[extern "lean_pod_Float32_atan"]
opaque atan : Float32 → Float32

@[extern "lean_pod_Float32_atan2"]
opaque atan2 : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_sinh"]
opaque sinh : Float32 → Float32

@[extern "lean_pod_Float32_cosh"]
opaque cosh : Float32 → Float32

@[extern "lean_pod_Float32_tanh"]
opaque tanh : Float32 → Float32

@[extern "lean_pod_Float32_asinh"]
opaque asinh : Float32 → Float32

@[extern "lean_pod_Float32_acosh"]
opaque acosh : Float32 → Float32

@[extern "lean_pod_Float32_atanh"]
opaque atanh : Float32 → Float32

@[extern "lean_pod_Float32_exp"]
opaque exp : Float32 → Float32

@[extern "lean_pod_Float32_exp2"]
opaque exp2 : Float32 → Float32

@[extern "lean_pod_Float32_log"]
opaque log : Float32 → Float32

@[extern "lean_pod_Float32_log2"]
opaque log2 : Float32 → Float32

@[extern "lean_pod_Float32_log10"]
opaque log10 : Float32 → Float32

@[extern "lean_pod_Float32_pow"]
opaque pow : Float32 → Float32 → Float32

@[extern "lean_pod_Float32_sqrt"]
opaque sqrt : Float32 → Float32

@[extern "lean_pod_Float32_cbrt"]
opaque cbrt : Float32 → Float32

@[extern "lean_pod_Float32_ceil"]
opaque ceil : Float32 → Float32

@[extern "lean_pod_Float32_floor"]
opaque floor : Float32 → Float32

@[extern "lean_pod_Float32_round"]
opaque round : Float32 → Float32

@[extern "lean_pod_Float32_abs"]
opaque abs : Float32 → Float32

/-- Efficiently computes `x * 2^i`. -/
@[extern "lean_pod_Float32_scaleB"]
opaque scaleB (x : Float32) (i : @& Int) : Float32

def ofBinaryScientific (m : Nat) (e : Int) : Float32 :=
  let s := m.log2 - 31
  let m := (m >>> s).toUInt32
  let e := e + s
  m.toFloat32.scaleB e

def ofScientific (m : Nat) (s : Bool) (e : Nat) : Float32 :=
  if s
    then
      let s := 32 - m.log2
      let m := (m <<< (3 * e + s)) / 5 ^ e
      ofBinaryScientific m (-4 * e - s)
    else
      ofBinaryScientific (m * 5 ^ e) e

def ofNat (n : Nat) : Float32 := ofScientific n false 0

end Pod.Float32

def Nat.toFloat32 (n : Nat) : Pod.Float32 := Pod.Float32.ofNat n

instance : ToString Pod.Float32 := ⟨Pod.Float32.toString⟩
instance : Repr Pod.Float32 := ⟨λ x _ ↦ x.toString⟩
instance : ReprAtom Pod.Float32 := ⟨⟩
instance {n} : OfNat Pod.Float32 n := ⟨n.toFloat32⟩

@[default_instance mid+1]
instance : OfScientific Pod.Float32 := ⟨Pod.Float32.ofScientific⟩

instance : LT Pod.Float32 where
  lt x y := Pod.Float32.blt x y

instance : LE Pod.Float32 where
  le x y := Pod.Float32.ble x y

instance {x y : Pod.Float32} : Decidable (x < y) :=
  if h : x.blt y then .isTrue h else .isFalse h

instance {x y : Pod.Float32} : Decidable (x ≤ y) :=
  if h : x.ble y then .isTrue h else .isFalse h

instance : Add Pod.Float32 := ⟨Pod.Float32.add⟩
instance : Sub Pod.Float32 := ⟨Pod.Float32.sub⟩
instance : Mul Pod.Float32 := ⟨Pod.Float32.mul⟩
instance : Div Pod.Float32 := ⟨Pod.Float32.div⟩
instance : Neg Pod.Float32 := ⟨Pod.Float32.neg⟩
instance : BEq Pod.Float32 := ⟨Pod.Float32.beq⟩
instance : Pow Pod.Float32 Pod.Float32 := ⟨Pod.Float32.pow⟩
instance : Min Pod.Float32 := ⟨Pod.Float32.min⟩
instance : Max Pod.Float32 := ⟨Pod.Float32.max⟩


/-! # Float -/

@[extern "lean_pod_Float_bits"]
opaque Float.bits : Float → UInt64
