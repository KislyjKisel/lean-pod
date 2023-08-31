namespace Pod

inductive Endianness where
  | little
  | big
deriving Repr, Inhabited

instance : DecidableEq Endianness
| .little, .little => isTrue rfl
| .little, .big => isFalse $ by intro; contradiction
| .big, .little => isFalse $ by intro; contradiction
| .big, .big => isTrue rfl

@[extern "lean_pod_getEndianness"]
private opaque getEndianness : Unit → Endianness

def endianness : Endianness := getEndianness ()
