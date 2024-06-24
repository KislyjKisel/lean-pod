import Pod.Meta
import Pod.Initialization
import Pod.BytesView
import Pod.BytesRef

namespace Pod

define_foreign_type Buffer (size align : Nat)

namespace Buffer

@[extern "lean_pod_Buffer_allocate"]
opaque allocate (size : @& Nat) : Buffer size 8

@[extern "lean_pod_Buffer_allocateClear"]
opaque allocateClear (size : @& Nat) : Buffer size 8

@[extern "lean_pod_Buffer_view"]
opaque view {size align : @& Nat} (buf : Buffer size align) : BytesView size align

@[extern "lean_pod_Buffer_withRef"]
opaque withRef {size align : @& Nat} (buf : Buffer size align) (f : ∀{σ}, BytesRefMut σ size align → ST σ Unit) : Buffer size align
