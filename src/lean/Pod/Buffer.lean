import Pod.BytesView
import Pod.BytesRef

namespace Pod

opaque BufferPointed (size align : Nat) : NonemptyType
def Buffer (size align : Nat) : Type := (BufferPointed size align).type
instance : Nonempty (Buffer size align) := (BufferPointed size align).property

namespace Buffer

@[extern "lean_pod_Buffer_allocate"]
opaque allocate (size : @& Nat) : Buffer size 8

@[extern "lean_pod_Buffer_allocateClear"]
opaque allocateClear (size : @& Nat) : Buffer size 8

@[extern "lean_pod_Buffer_view"]
opaque view {size align : @& Nat} (buf : Buffer size align) : BytesView size align

@[extern "lean_pod_Buffer_withRef"]
opaque withRef {size align : @& Nat} (buf : Buffer size align) (f : ∀{σ}, BytesRefMut σ size align → ST σ Unit) : Buffer size align
