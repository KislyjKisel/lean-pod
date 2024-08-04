import PodPrecompiled.Endianness

@[extern c inline "#1"]
def UInt8.ofBool (x : Bool) : UInt8 := cond x 1 0

@[extern "lean_pod_UInt16_bswap"]
def UInt16.bswap (value : UInt16) : UInt16 :=
  (value <<< 8) ||| (value >>> 8)

@[extern "lean_pod_UInt16_toBigEndian"]
def UInt16.toBigEndian (value : UInt16) :=
  if Pod.endianness = .big
    then value
    else value.bswap

@[extern "lean_pod_UInt16_toLittleEndian"]
def UInt16.toLittleEndian (value : UInt16) :=
  if Pod.endianness = .little
    then value
    else value.bswap

@[extern c inline "(uint16_t)#1"]
def UInt16.ofBool (x : Bool) : UInt16 := cond x 1 0

@[extern "lean_pod_UInt32_bswap"]
def UInt32.bswap (value : UInt32) : UInt32 :=
  ((value &&& 0x000000FF) <<< 24) |||
  ((value &&& 0x0000FF00) <<<  8) |||
  ((value &&& 0x00FF0000) >>>  8) |||
  ((value &&& 0xFF000000) >>> 24)

@[extern "lean_pod_UInt32_toBigEndian"]
def UInt32.toBigEndian (value : UInt32) :=
  if Pod.endianness = .big
    then value
    else value.bswap

@[extern "lean_pod_UInt32_toLittleEndian"]
def UInt32.toLittleEndian (value : UInt32) :=
  if Pod.endianness = .little
    then value
    else value.bswap

@[extern c inline "(uint32_t)#1"]
def UInt32.ofBool (x : Bool) : UInt32 := cond x 1 0

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

@[extern "lean_pod_UInt64_toBigEndian"]
def UInt64.toBigEndian (value : UInt64) :=
  if Pod.endianness = .big
    then value
    else value.bswap

@[extern "lean_pod_UInt64_toLittleEndian"]
def UInt64.toLittleEndian (value : UInt64) :=
  if Pod.endianness = .little
    then value
    else value.bswap

@[extern c inline "(uint64_t)#1"]
def UInt64.ofBool (x : Bool) : UInt64 := cond x 1 0

@[extern "lean_pod_USize_bswap"]
opaque USize.bswap (value : USize) : USize

@[extern "lean_pod_USize_toBigEndian"]
def USize.toBigEndian (value : USize) :=
  if Pod.endianness = .big
    then value
    else value.bswap

@[extern "lean_pod_USize_toLittleEndian"]
def USize.toLittleEndian (value : USize) :=
  if Pod.endianness = .little
    then value
    else value.bswap

@[extern c inline "(size_t)#1"]
def USize.ofBool (x : Bool) : USize := cond x (USize.ofNat32 1 $ by decide) (USize.ofNat32 0 $ by decide)
