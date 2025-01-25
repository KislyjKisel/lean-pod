import Pod.UInt
import Pod.Storable

namespace Pod

def Int8.sign (x : Int8) : Bool :=
  (x.toUInt8 &&& ((1 : UInt8) <<< 7)) > 0

def Int8.shr (x y : Int8) : Int8 :=
  ⟨⟨x.toBitVec >>> y.toBitVec⟩⟩

@[extern c inline "(double)(int8_t)#1"]
opaque Int8.toFloat (x : Int8) : Float

@[extern c inline "(int8_t)#1"]
opaque Int8.ofFloat (x : Float) : Int8

instance : Storable Int8 where
  byteSize := byteSize (α := UInt8)
  alignment := alignment (α := UInt8)

def Int16.sign (x : Int16) : Bool :=
  (x.toUInt16 &&& ((1 : UInt16) <<< 15)) > 0

def Int16.shr (x y : Int16) : Int16 :=
  ⟨⟨x.toBitVec >>> y.toBitVec⟩⟩

def Int16.bswap (x : Int16) : Int16 :=
  ⟨x.toUInt16.bswap⟩

def Int16.toLittleEndian (x : Int16) : Int16 :=
  ⟨x.toUInt16.toLittleEndian⟩

def Int16.toBigEndian (x : Int16) : Int16 :=
  ⟨x.toUInt16.toBigEndian⟩

@[extern c inline "(double)(int16_t)#1"]
opaque Int16.toFloat (x : Int16) : Float

@[extern c inline "(int16_t)#1"]
opaque Int16.ofFloat (x : Float) : Int16

instance : Storable Int16 where
  byteSize := byteSize (α := UInt16)
  alignment := alignment (α := UInt16)

def Int32.sign (x : Int32) : Bool :=
  (x.toUInt32 &&& ((1 : UInt32) <<< 31)) > 0

def Int32.shr (x y : Int32) : Int32 :=
  ⟨x.toUInt32 >>> y.toUInt32⟩

def Int32.bswap (x : Int32) : Int32 :=
  ⟨x.toUInt32.bswap⟩

def Int32.toLittleEndian (x : Int32) : Int32 :=
  ⟨x.toUInt32.toLittleEndian⟩

def Int32.toBigEndian (x : Int32) : Int32 :=
  ⟨x.toUInt32.toBigEndian⟩

@[extern c inline "(double)(int32_t)#1"]
opaque Int32.toFloat (x : Int32) : Float

@[extern c inline "(int32_t)#1"]
opaque Int32.ofFloat (x : Float) : Int32

instance : Storable Int32 where
  byteSize := byteSize (α := UInt32)
  alignment := alignment (α := UInt32)

def Int64.sign (x : Int64) : Bool :=
  (x.toUInt64 &&& ((1 : UInt64) <<< 63)) > 0

def Int64.shr (x y : Int64) : Int64 :=
  ⟨x.toUInt64 >>> y.toUInt64⟩

def Int64.bswap (x : Int64) : Int64 :=
  ⟨x.toUInt64.bswap⟩

def Int64.toLittleEndian (x : Int64) : Int64 :=
  ⟨x.toUInt64.toLittleEndian⟩

def Int64.toBigEndian (x : Int64) : Int64 :=
  ⟨x.toUInt64.toBigEndian⟩

@[extern c inline "(double)(int64_t)#1"]
opaque Int64.toFloat (x : Int64) : Float

@[extern c inline "(int64_t)#1"]
opaque Int64.ofFloat (x : Float) : Int64

instance : Storable Int64 where
  byteSize := byteSize (α := UInt64)
  alignment := alignment (α := UInt64)
  alignment_dvd_byteSize := alignment_dvd_byteSize (α := UInt64)
