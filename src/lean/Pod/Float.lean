import Pod.UInt
import Pod.Storable
import Pod.Int

namespace Float32

def inf : Float32 := .ofBits 0x7F800000
def negInf : Float32 := .ofBits 0xFF800000
def pi : Float32 := .ofBits 0x40490FDB

end Float32

@[extern "lean_pod_UInt8_toFloat32"]
opaque UInt8.toFloat32 : UInt8 → Float32

@[extern "lean_pod_UInt16_toFloat32"]
opaque UInt16.toFloat32 : UInt16 → Float32

@[extern "lean_pod_UInt32_toFloat32"]
opaque UInt32.toFloat32 : UInt32 → Float32

@[extern "lean_pod_USize_toFloat32"]
opaque USize.toFloat32 : USize → Float32

@[extern "lean_pod_Int8_toFloat32"]
opaque Int8.toFloat32 : Int8 → Float32

@[extern "lean_pod_Int16_toFloat32"]
opaque Int16.toFloat32 : Int16 → Float32

@[extern "lean_pod_Int32_toFloat32"]
opaque Int32.toFloat32 : Int32 → Float32

@[extern "lean_pod_Int64_toFloat32"]
opaque Int64.toFloat32 : Int64 → Float32

@[extern "lean_pod_String_toFloat32"]
opaque String.toFloat32? : @& String → Option Float32

@[extern "lean_pod_Substring_toFloat32"]
opaque Substring.toFloat32? : @& Substring → Option Float32

namespace Float32

@[extern "lean_pod_Float32_toInt8"]
opaque toInt8 : Float32 → Int8

@[extern "lean_pod_Float32_toInt16"]
opaque toInt16 : Float32 → Int16

@[extern "lean_pod_Float32_toInt32"]
opaque toInt32 : Float32 → Int32

@[extern "lean_pod_Float32_toInt64"]
opaque toInt64 : Float32 → Int64

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
