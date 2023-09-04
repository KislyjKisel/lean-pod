import Pod.UInt
import Pod.Storable

namespace Pod

structure Int8 where
  val : UInt8
deriving Inhabited, Repr

structure Int16 where
  val : UInt16
deriving Inhabited, Repr

structure Int32 where
  val : UInt32
deriving Inhabited, Repr

structure Int64 where
  val : UInt64
deriving Inhabited, Repr

def Int8.sign (x : Int8) : Bool := (x.val &&& ((1 : UInt8) <<< 7)) > 0

@[extern c inline "(int8_t)#1 * (int8_t)#2"]
opaque Int8.mul (x y : Int8) : Int8

@[extern c inline "(int8_t)#1 / (int8_t)#2"]
opaque Int8.div (x y : Int8) : Int8

@[extern c inline "(int8_t)#1 % (int8_t)#2"]
opaque Int8.mod (x y : Int8) : Int8

@[extern c inline "(int8_t)#1 >> (int8_t)#2"]
opaque Int8.sar (x y : Int8) : Int8

def Int8.shr (x y : Int8) : Int8 := .mk (x.val >>> y.val)

instance : AndOp Int8 where
  and x y := .mk $ x.val &&& y.val
instance : OrOp Int8 where
  or x y := .mk $ x.val ||| y.val
instance : Xor Int8 where
  xor x y := .mk $ x.val ^^^ y.val
instance : Complement Int8 where
  complement x := .mk x.val.complement
instance : ShiftLeft Int8 where
  shiftLeft x y := .mk (x.val <<< y.val)
instance : ShiftRight Int8 where
  shiftRight x y := x.sar y
instance : Add Int8 where
  add x y := .mk $ x.val + y.val
instance : Sub Int8 where
  sub x y := .mk $ x.val - y.val
instance : Neg Int8 where
  neg x := .mk (x.val - 1).complement
instance : Mul Int8 := ⟨Int8.mul⟩
instance : Div Int8 := ⟨Int8.div⟩
instance : Mod Int8 := ⟨Int8.mod⟩
instance : ToString Int8 where
  toString x := ite x.sign s!"-{toString (-x).val}" (toString x.val)
instance : BEq Int8 where
  beq x y := x.val == y.val
instance : Storable Int8 where
  byteSize := byteSize (α := UInt8)
  alignment := alignment (α := UInt8)

def Int16.sign (x : Int16) : Bool := (x.val &&& ((1 : UInt16) <<< 15)) > 0
def Int16.shr (x y : Int16) : Int16 := .mk (x.val >>> y.val)
def Int16.bswap (x : Int16) : Int16 := .mk x.val.bswap
def Int16.toLittleEndian (x : Int16) : Int16 := .mk x.val.toLittleEndian
def Int16.toBigEndian (x : Int16) : Int16 := .mk x.val.toBigEndian

@[extern c inline "(int16_t)#1 * (int16_t)#2"]
opaque Int16.mul (x y : Int16) : Int16

@[extern c inline "(int16_t)#1 / (int16_t)#2"]
opaque Int16.div (x y : Int16) : Int16

@[extern c inline "(int16_t)#1 % (int16_t)#2"]
opaque Int16.mod (x y : Int16) : Int16

@[extern c inline "(int16_t)#1 >> (int16_t)#2"]
opaque Int16.sar (x y : Int16) : Int16

instance : AndOp Int16 where
  and x y := .mk $ x.val &&& y.val
instance : OrOp Int16 where
  or x y := .mk $ x.val ||| y.val
instance : Xor Int16 where
  xor x y := .mk $ x.val ^^^ y.val
instance : Complement Int16 where
  complement x := .mk x.val.complement
instance : ShiftLeft Int16 where
  shiftLeft x y := .mk (x.val <<< y.val)
instance : ShiftRight Int16 where
  shiftRight x y := x.sar y
instance : Add Int16 where
  add x y := .mk $ x.val + y.val
instance : Sub Int16 where
  sub x y := .mk $ x.val - y.val
instance : Neg Int16 where
  neg x := .mk (x.val - 1).complement
instance : Mul Int16 := ⟨Int16.mul⟩
instance : Div Int16 := ⟨Int16.div⟩
instance : Mod Int16 := ⟨Int16.mod⟩
instance : ToString Int16 where
  toString x := ite x.sign s!"-{toString (-x).val}" (toString x.val)
instance : BEq Int16 where
  beq x y := x.val == y.val
instance : Storable Int16 where
  byteSize := byteSize (α := UInt16)
  alignment := alignment (α := UInt16)

def Int32.sign (x : Int32) : Bool := (x.val &&& ((1 : UInt32) <<< 31)) > 0
def Int32.shr (x y : Int32) : Int32 := .mk (x.val >>> y.val)
def Int32.bswap (x : Int32) : Int32 := .mk x.val.bswap
def Int32.toLittleEndian (x : Int32) : Int32 := .mk x.val.toLittleEndian
def Int32.toBigEndian (x : Int32) : Int32 := .mk x.val.toBigEndian

@[extern c inline "(int32_t)#1 * (int32_t)#2"]
opaque Int32.mul (x y : Int32) : Int32

@[extern c inline "(int32_t)#1 / (int32_t)#2"]
opaque Int32.div (x y : Int32) : Int32

@[extern c inline "(int32_t)#1 % (int32_t)#2"]
opaque Int32.mod (x y : Int32) : Int32

@[extern c inline "(int32_t)#1 >> (int32_t)#2"]
opaque Int32.sar (x y : Int32) : Int32

instance : AndOp Int32 where
  and x y := .mk $ x.val &&& y.val
instance : OrOp Int32 where
  or x y := .mk $ x.val ||| y.val
instance : Xor Int32 where
  xor x y := .mk $ x.val ^^^ y.val
instance : Complement Int32 where
  complement x := .mk x.val.complement
instance : ShiftLeft Int32 where
  shiftLeft x y := .mk (x.val <<< y.val)
instance : ShiftRight Int32 where
  shiftRight x y := x.sar y
instance : Add Int32 where
  add x y := .mk $ x.val + y.val
instance : Sub Int32 where
  sub x y := .mk $ x.val - y.val
instance : Neg Int32 where
  neg x := .mk (x.val - 1).complement
instance : Mul Int32 := ⟨Int32.mul⟩
instance : Div Int32 := ⟨Int32.div⟩
instance : Mod Int32 := ⟨Int32.mod⟩
instance : ToString Int32 where
  toString x := ite x.sign s!"-{toString (-x).val}" (toString x.val)
instance : BEq Int32 where
  beq x y := x.val == y.val
instance : Storable Int32 where
  byteSize := byteSize (α := UInt32)
  alignment := alignment (α := UInt32)

def Int64.sign (x : Int64) : Bool := (x.val &&& ((1 : UInt64) <<< 63)) > 0
def Int64.shr (x y : Int64) : Int64 := .mk (x.val >>> y.val)
def Int64.bswap (x : Int64) : Int64 := .mk x.val.bswap
def Int64.toLittleEndian (x : Int64) : Int64 := .mk x.val.toLittleEndian
def Int64.toBigEndian (x : Int64) : Int64 := .mk x.val.toBigEndian

@[extern c inline "(int64_t)#1 * (int64_t)#2"]
opaque Int64.mul (x y : Int64) : Int64

@[extern c inline "(int64_t)#1 / (int64_t)#2"]
opaque Int64.div (x y : Int64) : Int64

@[extern c inline "(int64_t)#1 % (int64_t)#2"]
opaque Int64.mod (x y : Int64) : Int64

@[extern c inline "(int64_t)#1 >> (int64_t)#2"]
opaque Int64.sar (x y : Int64) : Int64

instance : AndOp Int64 where
  and x y := .mk $ x.val &&& y.val
instance : OrOp Int64 where
  or x y := .mk $ x.val ||| y.val
instance : Xor Int64 where
  xor x y := .mk $ x.val ^^^ y.val
instance : Complement Int64 where
  complement x := .mk x.val.complement
instance : ShiftLeft Int64 where
  shiftLeft x y := .mk (x.val <<< y.val)
instance : ShiftRight Int64 where
  shiftRight x y := x.sar y
instance : Add Int64 where
  add x y := .mk $ x.val + y.val
instance : Sub Int64 where
  sub x y := .mk $ x.val - y.val
instance : Neg Int64 where
  neg x := .mk (x.val - 1).complement
instance : Mul Int64 := ⟨Int64.mul⟩
instance : Div Int64 := ⟨Int64.div⟩
instance : Mod Int64 := ⟨Int64.mod⟩
instance : ToString Int64 where
  toString x := ite x.sign s!"-{toString (-x).val}" (toString x.val)
instance : BEq Int64 where
  beq x y := x.val == y.val
instance : Storable Int64 where
  byteSize := byteSize (α := UInt64)
  alignment := alignment (α := UInt64)
  alignment_dvd_byteSize := alignment_dvd_byteSize (α := UInt64)