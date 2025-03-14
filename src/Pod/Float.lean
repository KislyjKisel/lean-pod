import Pod.UInt
import Pod.Storable
import Pod.Int

namespace Pod

namespace Float32

def inf : Float32 := .ofBits 0x7F800000
def negInf : Float32 := .ofBits 0xFF800000
def pi : Float32 := .ofBits 0x40490FDB

end Float32

@[extern "lean_pod_String_toFloat32"]
opaque String.toFloat32? : @& String → Option Float32

@[extern "lean_pod_Substring_toFloat32"]
opaque Substring.toFloat32? : @& Substring → Option Float32

namespace Float32

@[extern "lean_pod_Float32_isNormal"]
opaque isNormal : Float32 → Bool

@[extern "lean_pod_Float32_isUnordered"]
opaque isUnordered : Float32 → Float32 → Bool

def toLittleEndian : Float32 → Float32 :=
  Float32.ofBits ∘ UInt32.toLittleEndian ∘ Float32.toBits

def toBigEndian : Float32 → Float32 :=
  Float32.ofBits ∘ UInt32.toBigEndian ∘ Float32.toBits

end Float32

namespace Pod

instance : Storable Float32 where
  byteSize := byteSize UInt32
  alignment := alignment UInt32

end Pod

def Float.toLittleEndian : Float → Float :=
  Float.ofBits ∘ UInt64.toLittleEndian ∘ Float.toBits

def Float.toBigEndian : Float → Float :=
  Float.ofBits ∘ UInt64.toBigEndian ∘ Float.toBits
