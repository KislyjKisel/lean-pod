opaque BytesRefPointed (size : Nat) : NonemptyType
def BytesRef (size : Nat) : Type := (BytesRefPointed size).type
instance {size} : Nonempty (BytesRef size) := (BytesRefPointed size).property
