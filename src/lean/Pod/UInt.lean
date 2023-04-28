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

@[extern "lean_pod_USize_bswap"]
opaque USize.bswap (value : USize) : USize
