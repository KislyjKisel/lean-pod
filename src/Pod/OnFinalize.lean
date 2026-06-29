module

public meta import Pod.Meta

import Alloy.C

open scoped Alloy.C

alloy c include <lean/lean.h>

public section

namespace Pod

alloy c section

LEAN_EXPORT lean_obj_res lean_pod_touch(b_lean_obj_arg val, lean_obj_arg res) {
  return res;
}

static void lean_pod_OnFinalize_finalize(void* onFinalize) {
  lean_apply_1(onFinalize, lean_box(0));
}

static void lean_pod_OnFinalize_foreach(void* onFinalize, b_lean_obj_arg f) {
  lean_inc_ref(f);
  lean_inc_ref(onFinalize);
  lean_apply_1(f, onFinalize);
}

static void lean_pod_OnFinalizeMut_finalize(void* onFinalize) {
  if (onFinalize == NULL) return;
  lean_apply_1(onFinalize, lean_box(0));
}

static void lean_pod_OnFinalizeMut_foreach(void* onFinalize, b_lean_obj_arg f) {
  if (onFinalize == NULL) return;
  lean_inc_ref(f);
  lean_inc_ref(onFinalize);
  lean_apply_1(f, onFinalize);
}

end

/-- Noop. May be useful for artificially extending object lifetime when debugging. See also: `Runtime.hold`. -/
@[extern "lean_pod_touch"]
opaque touch {α β} (val : @& α) (res : β) : β := res

/-- Opaque immutable object wrapping a callback to be executed on its finalization. -/
alloy c opaque_extern_type OnFinalize => lean_object where
  foreach => "lean_pod_OnFinalize_foreach"
  finalize => "lean_pod_OnFinalize_finalize"

instance : Repr OnFinalize where
  reprPrec _ prec := Repr.addAppParen "onFinalize _" prec

/--
Creates an immutable finalization callback wrapper.
The callback will be called on wrapper's finalization.
-/
alloy c extern def onFinalize (callback : BaseIO Unit) : OnFinalize := {
  return to_lean<OnFinalize>(callback);
}

/-- Retrieves wrapper's assigned finalization callback. -/
alloy c extern def OnFinalize.get' (onFinalize : @& OnFinalize) : ULift.{0} (BaseIO Unit) := {
  lean_object* callback = of_lean<OnFinalize>(onFinalize);
  lean_inc_ref(callback);
  return callback;
}

@[inherit_doc OnFinalize.get']
abbrev OnFinalize.get := ULift.down ∘ OnFinalize.get'

/--
Opaque object wrapping a callback to be executed on its finalization.
Callback can be changed or removed from the object.
-/
alloy c opaque_extern_type OnFinalizeMut (σ : Type) => lean_object where
  foreach => "lean_pod_OnFinalizeMut_foreach"
  finalize => "lean_pod_OnFinalizeMut_finalize"

instance {σ} : Repr (OnFinalizeMut σ) where
  reprPrec _ prec := Repr.addAppParen "onFinalizeMut _" prec

/--
Creates a mutable finalization callback wrapper.
The callback will be called on wrapper's finalization.
-/
alloy c extern def onFinalizeMut {σ} (callback : Option <| BaseIO Unit) : ST σ (OnFinalizeMut σ) := {
  if (lean_is_scalar(callback)) {
    callback = NULL;
  }
  return to_lean<OnFinalizeMut>(callback);
}

/-- Retrieves currently assigned finalization callback. -/
alloy c extern def OnFinalizeMut.get {σ} (onFinalize : @& OnFinalizeMut σ) : ST σ (Option <| BaseIO Unit) := {
  lean_object* callback = of_lean<OnFinalizeMut>(onFinalize);
  if (callback == NULL) {
    return lean_box(0);
  }
  lean_inc_ref(callback);
  lean_object* result = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(result, 0, callback);
  return result;
}

/-- Replaces the object's finalization callback if any. -/
alloy c extern def OnFinalizeMut.setSome {σ} (onFinalize : @& OnFinalizeMut σ) (newCallback : BaseIO Unit) : ST σ Unit := {
  lean_object* callback = of_lean<OnFinalizeMut>(onFinalize);
  if (callback != NULL) {
    lean_dec_ref(callback);
  }
  lean_to_external(onFinalize)->m_data = newCallback;
  return lean_box(0);
}

/-- Removes the finalization callback from the object. Nothing will be done on finalization. -/
alloy c extern def OnFinalizeMut.suppress {σ} (onFinalize : @& OnFinalizeMut σ) : ST σ Unit := {
  lean_object* callback = of_lean<OnFinalizeMut>(onFinalize);
  if (callback != NULL) {
    lean_dec_ref(callback);
  }
  lean_to_external(onFinalize)->m_data = NULL;
  return lean_box(0);
}

@[inline]
def OnFinalizeMut.set {σ} (onFinalize : @& OnFinalizeMut σ) : (Option <| BaseIO Unit) → ST σ Unit
| none => onFinalize.suppress
| some cb => onFinalize.setSome cb
