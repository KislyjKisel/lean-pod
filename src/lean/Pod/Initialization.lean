import Pod.Meta

namespace Pod

extern_initialize => "lean_pod_initialize_types"

@[noinline]
def dummy {α} (x : α) : α := x
