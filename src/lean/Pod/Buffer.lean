import Pod.BytesView
import Pod.BytesRef

namespace Pod

opaque BufferPointed (size : USize) (align : Nat) : NonemptyType
def Buffer (size : USize) (align : Nat) : Type := (BufferPointed size align).type
instance : Nonempty (Buffer size align) := (BufferPointed size align).property

namespace Buffer 

@[extern "lean_pod_Buffer_allocate"]
opaque allocate (size : USize) : Buffer size 8

@[extern "lean_pod_Buffer_allocateClear"]
opaque allocateClear (size : USize) : Buffer size 8

@[extern "lean_pod_Buffer_view"]
opaque view {size} {align : @& Nat} (buf : Buffer size align) : BytesView size align

@[extern "lean_pod_Buffer_withRef"]
opaque withRef {size} {align : @& Nat} (buf : Buffer size align) (f : ∀{σ}, BytesRefMut σ size align → ST σ Unit) : Buffer size align
