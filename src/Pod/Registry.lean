import Std.Data.HashMap
import Pod.Array

namespace Pod

universe u
variable {ι : Type u}

/--
Collection of values indexed by opaque generated keys.
Both values and keys types are indexed by a parameter that is specified when inserting a new value.
-/
structure Registry (α : ι → Type) where
  private mk ::
  /--
  `IO.Ref` allows mutation while retaining identity.
  This is required for keys to have a type that depends on a registry value.

  Mutex is not required for basic `Registry` operations.
  `Mutex α  ~  BaseMutex × IO.Ref α`.
  Forcing mutex here introduces unnecessary overhead in cases when guarded
  state contains more than just the registry.
  But it means that a linear `modifyM` would need to be implemented in user code with `unsafe`.
  It seems that direct access to `IO.Ref` is not required for that.
  -/
  private data : IO.Ref (Array NonScalar)

class IsRegistryKey (α : ι → Type) where
  private mk ::
  private toNat : ∀ {i}, α i → Nat

@[always_inline, inline]
def IsRegistryKey.wrapper
  {ι ι'} {α : ι → Type} {β : ι' → Type} [IsRegistryKey α]
  (mapI : ι' → ι) (to : ∀ {i}, β i → α (mapI i))
  : IsRegistryKey β := {
    toNat := IsRegistryKey.toNat ∘ to
  }

def Registry.new {α : ι → Type} : BaseIO (Registry α) := do
  let data ← IO.mkRef #[]
  return { data }

structure Registry.Key {α : ι → Type} (reg : Registry α) (i : ι) where
  private mk ::
  private nonempty : Nonempty (α i)
  val : Nat

instance {α : ι → Type} {reg : Registry α} {i} [Nonempty (α i)] : Nonempty (Registry.Key reg i) :=
  .intro ⟨inferInstance, 0⟩

instance {α : ι → Type} {reg : Registry α} : IsRegistryKey (Registry.Key reg) where
  toNat k := k.val

private unsafe
def Registry.registerImpl {α : ι → Type} (reg : Registry α) {i} (x : α i) : BaseIO (Key reg i) :=
  Key.mk (.intro x) <$> reg.data.modifyGet λ data ↦ (data.size, data.push <| @unsafeCast (α i) NonScalar x)

@[implemented_by registerImpl]
opaque Registry.register {α : ι → Type} (reg : Registry α) {i} (x : α i) : BaseIO (Key reg i) :=
  pure ⟨.intro x, 0⟩

private unsafe
def Registry.Key.getImpl {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) : BaseIO (α i) := do
  pure <| @unsafeCast NonScalar (α i) <| (← reg.data.get)[key.val]'lcProof

@[implemented_by getImpl]
opaque Registry.Key.get {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) : BaseIO (α i) :=
  pure <| @Classical.ofNonempty _ key.nonempty

private unsafe
def Registry.Key.setImpl
  {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) (val : α i) : BaseIO Unit := do
    reg.data.modify λ xs ↦ xs.set key.val (@unsafeCast (α i) NonScalar val) lcProof

@[implemented_by setImpl]
opaque Registry.Key.set
  {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) (val : α i) : BaseIO Unit

private unsafe
def Registry.Key.modifyImpl
  {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) (f : α i → α i) : BaseIO Unit :=
    reg.data.modify λ xs ↦ xs.modify key.val λ x ↦
      @unsafeCast (α i) NonScalar <| f <| @unsafeCast NonScalar (α i) x

@[implemented_by modifyImpl]
opaque Registry.Key.modify
  {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) (f : α i → α i) : BaseIO Unit

private unsafe
def Registry.Key.modifyGetImpl
  {α : ι → Type} {β} [Nonempty β] {reg : Registry α} {i}
  (key : Key reg i) (f : α i → β × α i) : BaseIO β :=
    reg.data.modifyGet λ xs ↦ Pod.Array.modifyGet xs key.val lcProof λ x ↦
      let (res, x) := f <| @unsafeCast NonScalar (α i) x
      (res, @unsafeCast (α i) NonScalar <| x)

@[implemented_by modifyGetImpl]
opaque Registry.Key.modifyGet
  {α : ι → Type} {β} [Nonempty β] {reg : Registry α} {i}
  (key : Key reg i) (f : α i → β × α i) : BaseIO β

private unsafe
def Registry.Key.modifyIoImpl
  {α : ι → Type} {reg : Registry α} {i}
  (key : Key reg i) (f : α i → BaseIO (α i)) : BaseIO Unit := do
    let data ← reg.data.take -- `Ref.take` is marked unsafe, why?
    let data ← data.modifyM key.val λ x ↦
      @unsafeCast (α i) NonScalar <$> (f <| @unsafeCast NonScalar (α i) x)
    reg.data.set data -- Always called because `BaseIO` can't throw.

@[implemented_by modifyIoImpl]
unsafe opaque Registry.Key.modifyIo
  {α : ι → Type} {reg : Registry α} {i}
  (key : Key reg i) (f : α i → BaseIO (α i)) : BaseIO Unit

private unsafe
def Registry.Key.modifyGetIoImpl
  {α : ι → Type} {β} [Nonempty β] {reg : Registry α} {i}
  (key : Key reg i) (f : α i → BaseIO (β × α i)) : BaseIO β := do
    let data ← reg.data.take -- `Ref.take` is marked unsafe, why?
    let (res, data) ← Pod.Array.modifyGetIo data key.val lcProof λ x ↦ do
      let (res, x) ← f <| @unsafeCast NonScalar (α i) x
      pure (res, @unsafeCast (α i) NonScalar x)
    reg.data.set data -- Always called because `BaseIO` can't throw.
    pure res

@[implemented_by modifyGetIoImpl]
unsafe opaque Registry.Key.modifyGetIo
  {α : ι → Type} {β} [Nonempty β] {reg : Registry α} {i}
  (key : Key reg i) (f : α i → BaseIO (β × α i)) : BaseIO β


/--
As if `∃ i, Key reg i`.
But storing `i` would cause a universe bump.
Is it safe?
I guess it is similar to `Dynamic` and should be safe.
-/
structure Registry.DynKey {α : ι → Type} (reg : Registry α) where
  private mk ::
  val : Nat

instance {α : ι → Type} {reg : Registry α} : Nonempty (Registry.DynKey reg) :=
  .intro ⟨0⟩

@[inline]
def Registry.Key.toDyn {α : ι → Type} {reg : Registry α} {i} (key : Key reg i) : DynKey reg :=
  ⟨key.val⟩

/-- Safe iff `key` was created from `Key reg i` (same `i`). -/
unsafe
def Registry.DynKey.unsafeGet {α : ι → Type} {reg : Registry α} (key : DynKey reg) (i : ι) : Key reg i :=
  { nonempty := lcProof, val := key.val }



variable {α : ι → Type} {β : ∀ {i}, α i → Type} {reg : Registry α}

structure Registry.Downstream (α : ι → Type) (β : ∀ {i}, α i → Type) where
  private mk ::
  /-- `∀ i, (k : α i) → β k` -/
  private init : NonScalar
  /-- Maps `k : α i` to `β k`. See `Registry.data`. -/
  private data : IO.Ref (Std.HashMap Nat NonScalar)

instance : Nonempty (Registry.Downstream α β) :=
  .intro { init := Classical.ofNonempty, data := Classical.ofNonempty }

namespace Registry.Downstream

private unsafe
def init' (reg : Downstream α β) : ∀ i, (k : α i) → β k :=
  unsafeCast reg.init

private unsafe
def newImpl (init : ∀ i, (k : α i) → β k) : BaseIO (Downstream α β) := do
  let data ← IO.mkRef .empty
  pure {
    init := unsafeCast init
    data
  }

@[implemented_by newImpl]
opaque new (init : ∀ i, (k : α i) → β k) : BaseIO (Downstream α β)

@[specialize] private unsafe
def modifyGetImpl
  {γ} [Nonempty γ] [irk : IsRegistryKey α]
  (reg : Registry.Downstream α β) {i} (key : α i) (f : β key → γ × β key) : BaseIO γ := do
    reg.data.modifyGet λ data ↦
      let key' := irk.toNat key
      let (value, data) :=
        match data.get? key' with
        | none => (reg.init' i key, data)
        | some value => (@unsafeCast NonScalar (β key) value, data.erase key')
      let (res, value) := f value
      (res, data.insert key' (@unsafeCast (β key) NonScalar value))

@[implemented_by modifyGetImpl]
opaque modifyGet
  {γ} [Nonempty γ] [irk : IsRegistryKey α]
  (reg : Registry.Downstream α β) {i} (key : α i) (f : β key → γ × β key) : BaseIO γ

@[inline]
def get
  [irk : IsRegistryKey α] (reg : Registry.Downstream α β) {i} (key : α i) [Nonempty (β key)]
  : BaseIO (β key) :=
    reg.modifyGet key (λ x ↦ (x, x))

@[inline]
def set
  [irk : IsRegistryKey α] (reg : Registry.Downstream α β) {i} (key : α i) (value : β key)
  : BaseIO Unit :=
    reg.modifyGet key (λ _ ↦ ((), value))

@[inline]
def modify
  [irk : IsRegistryKey α]
  (reg : Registry.Downstream α β) {i} (key : α i) (f : β key → β key) : BaseIO Unit :=
    reg.modifyGet key λ x ↦ ((), f x)
