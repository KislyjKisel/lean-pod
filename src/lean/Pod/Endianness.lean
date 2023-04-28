namespace Pod

inductive Endianness where
  | LittleEndian
  | BigEndian
deriving Repr, Inhabited

@[extern "lean_pod_getEndianness"]
private opaque getEndianness : Unit → Endianness

def endianness : Endianness := getEndianness ()
