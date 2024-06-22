import Pod.Meta

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

define_foreign_constant endianness : Endianness := "lean_pod_getEndianness"
