structure Float32 where
  val : UInt32

namespace Float32

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

instance : Inhabited Float32 := ⟨.zero⟩

@[extern "lean_pod_Float_toFloat32"]
opaque Float.toFloat32 : Float → Float32

@[extern "lean_pod_UInt8_toFloat32"]
opaque UInt8.toFloat32 : UInt8 → Float32

@[extern "lean_pod_UInt16_toFloat32"]
opaque UInt16.toFloat32 : UInt16 → Float32

@[extern "lean_pod_UInt32_toFloat32"]
opaque UInt32.toFloat32 : UInt32 → Float32

@[extern "lean_pod_UInt64_toFloat32"]
opaque UInt64.toFloat32 : UInt64 → Float32

@[extern "lean_pod_USize_toFloat32"]
opaque USize.toFloat32 : USize → Float32

namespace Float32

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

@[extern "sinf"]
opaque sin : Float32 → Float32

@[extern "cosf"]
opaque cos : Float32 → Float32

@[extern "tanf"]
opaque tan : Float32 → Float32

@[extern "asinf"]
opaque asin : Float32 → Float32

@[extern "acosf"]
opaque acos : Float32 → Float32

@[extern "atanf"]
opaque atan : Float32 → Float32

@[extern "atan2f"]
opaque atan2 : Float32 → Float32 → Float32

@[extern "asinhf"]
opaque sinh : Float32 → Float32

@[extern "acoshf"]
opaque cosh : Float32 → Float32

@[extern "atanhf"]
opaque tanh : Float32 → Float32

@[extern "asinhf"]
opaque asinh : Float32 → Float32

@[extern "acoshf"]
opaque acosh : Float32 → Float32

@[extern "atanhf"]
opaque atanh : Float32 → Float32

@[extern "expf"]
opaque exp : Float32 → Float32

@[extern "exp2f"]
opaque exp2 : Float32 → Float32

@[extern "logf"]
opaque log : Float32 → Float32

@[extern "log2f"]
opaque log2 : Float32 → Float32

@[extern "log10f"]
opaque log10 : Float32 → Float32

@[extern "powf"]
opaque pow : Float32 → Float32 → Float32

@[extern "sqrtf"]
opaque sqrt : Float32 → Float32

@[extern "cbrtf"]
opaque cbrt : Float32 → Float32

@[extern "ceilf"]
opaque ceil : Float32 → Float32

@[extern "floorf"]
opaque floor : Float32 → Float32

@[extern "roundf"]
opaque round : Float32 → Float32

@[extern "fabsf"]
opaque abs : Float32 → Float32

/-- Efficiently computes `x * 2^i`. -/
@[extern "lean_pod_Float32_scaleB"]
opaque scaleB (x : Float32) (i : @& Int) : Float32

end Float32

instance : ToString Float32 := ⟨Float32.toString⟩
instance : Repr Float32 := ⟨λ x _ ↦ x.toString⟩
instance : ReprAtom Float32 := ⟨⟩
instance {n} : OfNat Float32 n := ⟨(Float.ofNat n).toFloat32⟩

instance : OfScientific Float32 where
  ofScientific m s e := Float.toFloat32 (Float.ofScientific m s e)

instance : LT Float32 where
  lt x y := Float32.blt x y

instance : LE Float32 where
  le x y := Float32.ble x y

instance {x y : Float32} : Decidable (x < y) :=
  if h : x.blt y then .isTrue h else .isFalse h

instance {x y : Float32} : Decidable (x ≤ y) :=
  if h : x.ble y then .isTrue h else .isFalse h

instance : Add Float32 := ⟨Float32.add⟩
instance : Sub Float32 := ⟨Float32.sub⟩
instance : Mul Float32 := ⟨Float32.mul⟩
instance : Div Float32 := ⟨Float32.div⟩
instance : Neg Float32 := ⟨Float32.neg⟩
instance : BEq Float32 := ⟨Float32.beq⟩
instance : Pow Float32 Float32 := ⟨Float32.pow⟩
instance : Min Float32 := ⟨Float32.min⟩
instance : Max Float32 := ⟨Float32.max⟩
