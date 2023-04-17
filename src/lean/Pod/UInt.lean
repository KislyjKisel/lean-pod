@[extern "lean_pod_UInt16_bswap"]
def UInt16.bswap (value : UInt16) : UInt16 :=
  (value <<< 8) ||| (value >>> 8)

@[extern "lean_pod_UInt32_bswap"]
def UInt32.bswap (value : UInt32) : UInt32 :=
  ((value &&& 0x000000FF) <<< 24) |||
  ((value &&& 0x0000FF00) <<<  8) |||
  ((value &&& 0x00FF0000) >>>  8) |||
  ((value &&& 0xFF000000) >>> 24)

@[extern "lean_pod_UInt64_bswap"]
def UInt64.bswap (value : UInt64) : UInt64 :=
  ((value &&& 0xFF00000000000000) >>> 56) |||
  ((value &&& 0x00FF000000000000) >>> 40) |||
  ((value &&& 0x0000FF0000000000) >>> 24) |||
  ((value &&& 0x000000FF00000000) >>>  8) |||
  ((value &&& 0x00000000FF000000) <<<  8) |||
  ((value &&& 0x0000000000FF0000) <<< 24) |||
  ((value &&& 0x000000000000FF00) <<< 40) |||
  ((value &&& 0x00000000000000FF) <<< 56)

def UInt8.bitWidth : Nat := 8
def UInt8.byteWidth : Nat := 1
def UInt8.alignment : Nat := 1

def UInt16.bitWidth : Nat := 16
def UInt16.byteWidth : Nat := 2
def UInt16.alignment : Nat := 2

def UInt32.bitWidth : Nat := 32
def UInt32.byteWidth : Nat := 4
def UInt32.alignment : Nat := 4

@[extern "lean_pod_UInt64_getAlignment"]
opaque UInt64.getAlignment : @& Unit → { n : Nat // n = 4 ∨ n = 8 } := λ _ ↦ ⟨8, Or.inr rfl⟩

def UInt64.bitWidth : Nat := 64
def UInt64.byteWidth : Nat := 8
def UInt64.alignment : Nat := UInt64.getAlignment ()

def USize.bitWidth : Nat := System.Platform.numBits
def USize.byteWidth : Nat := System.Platform.numBits / 8
def USize.alignment : Nat := if System.Platform.numBits = 32 then 4 else 8
