import Pod.Meta

namespace Pod

universe u
variable {α : Type u}

define_foreign_type Deque (α : Type u) : Type u

namespace Deque

@[extern "lean_pod_Deque_ofList"]
opaque ofList (xs : @& List α) : Deque α

@[extern "lean_pod_Deque_toList"]
opaque toList (deque : @& Deque α) : List α

@[extern "lean_pod_Deque_mkEmpty"]
def mkEmpty (capacity : @& Nat) : Deque α :=
  .ofList .nil

set_option compiler.extract_closed false in
def empty : Deque α :=
  mkEmpty 0

set_option compiler.extract_closed false in
instance : Inhabited (Deque α) := ⟨empty⟩

@[extern "lean_pod_Deque_singleton"]
def singleton (x : α) : Deque α :=
  .ofList [x]

@[extern "lean_pod_Deque_replicate"]
def replicate (n : @& Nat) (x : @& α) : Deque α :=
  .ofList $ List.replicate n x

@[extern "lean_pod_Deque_toArray"]
def toArray (deque : @& Deque α) : Array α :=
  deque.toList.toArray

@[extern "lean_pod_Deque_ofArray"]
def ofArray (a : @& Array α) : Deque α :=
  .ofList a.toList

@[extern "lean_pod_Deque_isEmpty"]
def isEmpty (deque : @& Deque α) : Bool :=
  deque.toList.isEmpty

@[extern "lean_pod_Deque_size"]
def size (deque : @& Deque α) : Nat :=
  deque.toList.length

theorem not_isEmpty_iff_size_pos {deque : Deque α} : ¬ deque.isEmpty ↔ deque.size > 0 := by
  show ¬ deque.toList.isEmpty ↔ deque.toList.length > 0
  cases deque.toList
  all_goals apply Iff.intro <;> (intro; try (intro; contradiction))
  · have : ([] : List α).isEmpty := rfl; contradiction
  · exact Nat.zero_lt_succ _

theorem not_isEmpty_iff_toList_ne_nil {deque : Deque α} : ¬ deque.isEmpty ↔ deque.toList ≠ [] := by
  show ¬ deque.toList.isEmpty ↔ _
  cases deque.toList <;>
    apply Iff.intro <;>
    (intro; intro; contradiction)

@[extern "lean_pod_Deque_pushBack"]
def pushBack (deque : Deque α) (x : α) : Deque α := .ofList (deque.toList ++ [x])

@[extern "lean_pod_Deque_pushFront"]
def pushFront (deque : Deque α) (x : α) : Deque α := .ofList (x :: deque.toList)

@[extern "lean_pod_Deque_peekBack"]
def peekBack (deque : @& Deque α) (h : ¬ deque.isEmpty) : α :=
  deque.toList.getLast $ not_isEmpty_iff_toList_ne_nil.mp h

def peekBack! [Inhabited α] (deque : Deque α) : α :=
  if h: ¬ deque.isEmpty
    then deque.peekBack h
    else panic! "Deque is empty"

def peekBack? (deque : Deque α) : Option α :=
  if h: ¬ deque.isEmpty
    then some (deque.peekBack h)
    else none

@[extern "lean_pod_Deque_peekFront"]
def peekFront (deque : @& Deque α) (h : ¬ deque.isEmpty) : α :=
  deque.toList.head $ not_isEmpty_iff_toList_ne_nil.mp h

def peekFront! [Inhabited α] (deque : Deque α) : α :=
  if h: ¬ deque.isEmpty
    then deque.peekFront h
    else panic! "Deque is empty"

def peekFront? (deque : Deque α) : Option α :=
  if h: ¬ deque.isEmpty
    then some (deque.peekFront h)
    else none

@[extern "lean_pod_Deque_popBack"]
def popBack (deque : Deque α) (h : ¬ deque.isEmpty) : Deque α :=
  .ofList deque.toList.dropLast

set_option compiler.extract_closed false in
def popBack! (deque : Deque α) : Deque α :=
  if h: deque.isEmpty
    then panic! "Deque is empty"
    else deque.popBack h

def popBack? (deque : Deque α) : Option (Deque α) :=
  if h: deque.isEmpty
    then none
    else deque.popBack h

def popBackD (deque : Deque α) : Deque α :=
  if h: deque.isEmpty
    then deque
    else deque.popBack h

@[extern "lean_pod_Deque_popFront"]
def popFront (deque : Deque α) (h : ¬ deque.isEmpty) : Deque α :=
  .ofList (deque.toList.tailD [])

set_option compiler.extract_closed false in
def popFront! (deque : Deque α) : Deque α :=
  if h: deque.isEmpty
    then panic! "Deque is empty"
    else deque.popFront h

def popFront? (deque : Deque α) : Option (Deque α) :=
  if h: deque.isEmpty
    then none
    else deque.popFront h

def popFrontD (deque : Deque α) : Deque α :=
  if h: deque.isEmpty
    then deque
    else deque.popFront h

@[extern "lean_pod_Deque_clear"]
def clear (deque : Deque α) : Deque α :=
  .empty

@[extern "lean_pod_Deque_get"]
def get (deque : @& Deque α) (i : @& Fin deque.size) : α :=
  deque.toList.get i

def getD (deque : Deque α) (i : Nat) (x : α) : α :=
  if h: i < deque.size
    then deque.get $ Fin.mk i h
    else x

def get? (deque : Deque α) (i : Nat) : Option α :=
  if h: i < deque.size
    then some $ deque.get $ Fin.mk i h
    else none

def get! [Inhabited α] (deque : Deque α) (i : Nat) : α :=
  if h: i < deque.size
    then deque.get $ Fin.mk i h
    else panic! "Index out of bounds"

@[extern "lean_pod_Deque_set"]
def set (deque : Deque α) (i : @& Fin deque.size) (x : α) : Deque α :=
  .ofList $ deque.toList.set i x

def setD (deque : Deque α) (i : Nat) (x : α) : Deque α :=
  if h: i < deque.size
    then deque.set (Fin.mk i h) x
    else deque

set_option compiler.extract_closed false in
def set! (deque : Deque α) (i : Nat) (x : α) : Deque α :=
  if h: i < deque.size
    then deque.set (Fin.mk i h) x
    else panic! "Index out of bounds"

instance [Repr α] : Repr (Deque α) where
  reprPrec deque _ := s!"\{ toList := {repr deque.toList}}"

set_option compiler.extract_closed false in
instance : EmptyCollection (Deque α) where
  emptyCollection := empty

instance : Singleton α (Deque α) where
  singleton := singleton

end Deque
