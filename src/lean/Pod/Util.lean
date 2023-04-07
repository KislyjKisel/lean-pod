def mb? {p α} [Decidable p] (f : p → α) : Option α :=
  if h : p then some $ f h else none

def mb! (err : String) {p α} [Decidable p] [Inhabited α] (f : p → α) : α :=
  if h : p then f h else panic! err
