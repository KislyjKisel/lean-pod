import Pod.UInt
import Pod.Storable

namespace Pod

def Int8.sign (x : Int8) : Bool :=
  (x.toUInt8 &&& ((1 : UInt8) <<< 7)) > 0

def Int8.shr (x y : Int8) : Int8 :=
  (x.toUInt8 >>> y.toUInt8).toInt8

instance : Storable Int8 where
  byteSize := byteSize (α := UInt8)
  alignment := alignment (α := UInt8)

def Int16.sign (x : Int16) : Bool :=
  (x.toUInt16 &&& ((1 : UInt16) <<< 15)) > 0

def Int16.shr (x y : Int16) : Int16 :=
  (x.toUInt16 >>> y.toUInt16).toInt16

def Int16.bswap (x : Int16) : Int16 :=
  x.toUInt16.bswap.toInt16

def Int16.toLittleEndian (x : Int16) : Int16 :=
  x.toUInt16.toLittleEndian.toInt16

def Int16.toBigEndian (x : Int16) : Int16 :=
  x.toUInt16.toBigEndian.toInt16

instance : Storable Int16 where
  byteSize := byteSize (α := UInt16)
  alignment := alignment (α := UInt16)

def Int32.sign (x : Int32) : Bool :=
  (x.toUInt32 &&& ((1 : UInt32) <<< 31)) > 0

def Int32.shr (x y : Int32) : Int32 :=
  (x.toUInt32 >>> y.toUInt32).toInt32

def Int32.bswap (x : Int32) : Int32 :=
  x.toUInt32.bswap.toInt32

def Int32.toLittleEndian (x : Int32) : Int32 :=
  x.toUInt32.toLittleEndian.toInt32

def Int32.toBigEndian (x : Int32) : Int32 :=
  x.toUInt32.toBigEndian.toInt32

instance : Storable Int32 where
  byteSize := byteSize (α := UInt32)
  alignment := alignment (α := UInt32)

def Int64.sign (x : Int64) : Bool :=
  (x.toUInt64 &&& ((1 : UInt64) <<< 63)) > 0

def Int64.shr (x y : Int64) : Int64 :=
  (x.toUInt64 >>> y.toUInt64).toInt64

def Int64.bswap (x : Int64) : Int64 :=
  x.toUInt64.bswap.toInt64

def Int64.toLittleEndian (x : Int64) : Int64 :=
  x.toUInt64.toLittleEndian.toInt64

def Int64.toBigEndian (x : Int64) : Int64 :=
  x.toUInt64.toBigEndian.toInt64

instance : Storable Int64 where
  byteSize := byteSize (α := UInt64)
  alignment := alignment (α := UInt64)
  alignment_dvd_byteSize := alignment_dvd_byteSize (α := UInt64)
