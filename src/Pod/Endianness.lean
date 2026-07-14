module

import Alloy.C
import Pod.Alloy

open scoped Alloy.C
open scoped Pod.Alloy

alloy c include <lean/lean.h>

public section

namespace Pod

inductive Endianness where
  | little
  | big
deriving Repr, Inhabited

instance : DecidableEq Endianness
  | .little, .little => isTrue rfl
  | .little, .big => isFalse <| by intro; contradiction
  | .big, .little => isFalse <| by intro; contradiction
  | .big, .big => isTrue rfl

define_foreign_constant endianness : Endianness := alloy c {
  #if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    return 0;
  /**/
  #elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    return 1;
  /**/
  #else
    #error unsupported
  #endif
}
