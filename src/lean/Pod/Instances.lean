import Lean.Elab.Command
import Pod.Lemmas
import Pod.Float
import Pod.Storable
import Pod.ReadBytes
import Pod.WriteBytes

open Lean Syntax
open Lean Elab Command

namespace Pod

section Instances

set_option maxRecDepth 1024

scoped elab "def_rwbytes_inst" typeName:str : command => do
  let typeStr := typeName.getString
  let typeId := mkIdent $ Name.mkSimple typeStr

  let declStr := "readBytesRef_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rra0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rra0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} (br : @& BytesRefImm σ (byteSize $typeId) (alignment $typeId)) : ST σ $typeId
  )

  let declStr := "readBytesRefOff_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rra1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rra1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
      (h₁ : i + (byteSize $typeId) ≤ size)
      (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) : ST σ $typeId
  )

  let declStr := "readBytesRefOffEl_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rra2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rra2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size : @& Nat} (br : @& BytesRefImm σ size (alignment $typeId)) (i : @& Nat)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ $typeId
  )

  let declStr := "readBytesRefUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rru0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rru0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {align : @& Nat} (br : @& BytesRefImm σ (byteSize $typeId) align) : ST σ $typeId
  )

  let declStr := "readBytesRefOffUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rru1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rru1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
      (h₁ : i + (byteSize $typeId) ≤ size) : ST σ $typeId
  )

  let declStr := "readBytesRefOffElUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rru2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rru2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ $typeId
  )

  let declStr := "readBytesView_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_va0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_va0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) (bv : @& BytesView (byteSize $typeId) (alignment $typeId)) : $typeId
  )

  let declStr := "readBytesViewOff_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_va1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_va1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
      (h₁ : i + (byteSize $typeId) ≤ size)
      (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) : $typeId
  )

  let declStr := "readBytesViewOffEl_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_va2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_va2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {size : @& Nat} (bv : @& BytesView size (alignment $typeId)) (i : @& Nat)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : $typeId
  )

  let declStr := "readBytesViewUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_vu0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_vu0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {align : @& Nat} (bv : @& BytesView (byteSize $typeId) align) : $typeId
  )

  let declStr := "readBytesViewOffUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_vu1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_vu1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
      (h₁ : i + (byteSize $typeId) ≤ size) : $typeId
  )

  let declStr := "readBytesViewOffElUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_vu2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_vu2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : $typeId
  )

  let declStr := "writeBytesRef_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwa0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwa0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ}
      (br : @& BytesRefMut σ (byteSize $typeId) (alignment $typeId)) (value : $typeId) :
      ST σ Unit
  )

  let declStr := "writeBytesRefOff_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwa1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwa1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat}
      (br : @& BytesRefMut σ size align) (i : @& Nat) (value : $typeId)
      (h₁ : i + (byteSize $typeId) ≤ size)
      (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) :
      ST σ Unit
  )

  let declStr := "writeBytesRefOffEl_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwa2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwa2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size : @& Nat}
      (br : @& BytesRefMut σ size (alignment $typeId)) (i : @& Nat) (value : $typeId)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) :
      ST σ Unit
  )

  let declStr := "writeBytesRefUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwu0 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwu0 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {align : @& Nat}
      (br : @& BytesRefMut σ (byteSize $typeId) align) (value : $typeId) :
      ST σ Unit
  )

  let declStr := "writeBytesRefOffUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwu1 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwu1 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat}
      (br : @& BytesRefMut σ size align) (i : @& Nat) (value : $typeId)
      (h₁ : i + (byteSize $typeId) ≤ size) :
      ST σ Unit
  )

  let declStr := "writeBytesRefOffElUnal_" ++ typeStr
  let declName := Name.mkSimple $ declStr
  let declName_rwu2 := `Pod ++ declName
  setEnv $ ← ofExcept $ externAttr.setParam (← getEnv) declName_rwu2 $
    ExternAttrData.mk none $ [ExternEntry.standard `all s!"lean_pod_{declStr}"]
  Lean.Elab.Command.elabCommand $ ← `(command|
    opaque $(mkIdent declName) {σ} {size align : @& Nat}
      (br : @& BytesRefMut σ size align) (i : @& Nat) (value : $typeId)
      (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) :
      ST σ Unit
  )


  Lean.Elab.Command.elabCommand $ ← `(command|
    instance : ReadBytes $typeId where
      readBytesRefOffUnal := $(mkIdent declName_rru1)
      readBytesRefUnal := $(mkIdent declName_rru0)
      readBytesRefOffElUnal := $(mkIdent declName_rru2)
      readBytesRefOff := $(mkIdent declName_rra1)
      readBytesRef := $(mkIdent declName_rra0)
      readBytesRefOffEl := $(mkIdent declName_rra2)
      readBytesViewOffUnal := $(mkIdent declName_vu1)
      readBytesViewUnal := $(mkIdent declName_vu0)
      readBytesViewOffElUnal := $(mkIdent declName_vu2)
      readBytesViewOff := $(mkIdent declName_va1)
      readBytesView := $(mkIdent declName_va0)
      readBytesViewOffEl := $(mkIdent declName_va2)
  )
  Lean.Elab.Command.elabCommand $ ← `(command|
    instance : WriteBytes $typeId where
      writeBytesRefOffUnal := $(mkIdent declName_rwu1)
      writeBytesRefUnal := $(mkIdent declName_rwu0)
      writeBytesRefOffElUnal := $(mkIdent declName_rwu2)
      writeBytesRefOff := $(mkIdent declName_rwa1)
      writeBytesRef := $(mkIdent declName_rwa0)
      writeBytesRefOffEl := $(mkIdent declName_rwa2)
  )

def_rwbytes_inst "UInt8"
def_rwbytes_inst "UInt16"
def_rwbytes_inst "UInt32"
def_rwbytes_inst "UInt64"
def_rwbytes_inst "USize"
def_rwbytes_inst "Float"
def_rwbytes_inst "Float32"

instance {size alignment} : GetElem (Pod.BytesView size alignment) Nat UInt8 λ _ i ↦ i < size where
  getElem bv i h := Pod.readBytesViewOff_UInt8 bv i h
    λ m ↦ Exists.intro (alignment * m + i) $ by
      show alignment * m + i = 1 * (alignment * m + i)
      rw [Nat.one_mul (alignment * m + i)]
