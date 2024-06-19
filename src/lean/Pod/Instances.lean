import Lean.Syntax
import Pod.Float
import Pod.Storable
import Pod.ReadBytes
import Pod.WriteBytes
import Pod.Serializable

open Lean Syntax

namespace Pod

section Instances

macro "#pod_c_rwbytes_instance" typeId:ident : command => do
  let typeStr := typeId.getId.toStringWithSep "_" false
  let declName_rra0 := "readBytesRef_" ++ typeStr
  let declName_rra1 := "readBytesRefOff_" ++ typeStr
  let declName_rra2 := "readBytesRefOffEl_" ++ typeStr
  let declName_rru0 := "readBytesRefUnal_" ++ typeStr
  let declName_rru1 := "readBytesRefOffUnal_" ++ typeStr
  let declName_rru2 := "readBytesRefOffElUnal_" ++ typeStr
  let declName_va0 := "readBytesView_" ++ typeStr
  let declName_va1 := "readBytesViewOff_" ++ typeStr
  let declName_va2 := "readBytesViewOffEl_" ++ typeStr
  let declName_vu0 := "readBytesViewUnal_" ++ typeStr
  let declName_vu1 := "readBytesViewOffUnal_" ++ typeStr
  let declName_vu2 := "readBytesViewOffElUnal_" ++ typeStr
  let declName_rwa0 := "writeBytesRef_" ++ typeStr
  let declName_rwa1 := "writeBytesRefOff_" ++ typeStr
  let declName_rwa2 := "writeBytesRefOffEl_" ++ typeStr
  let declName_rwu0 := "writeBytesRefUnal_" ++ typeStr
  let declName_rwu1 := "writeBytesRefOffUnal_" ++ typeStr
  let declName_rwu2 := "writeBytesRefOffElUnal_" ++ typeStr
  pure $ TSyntax.mk $ mkNullNode #[
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rra0):str]
      opaque $(mkIdent $ Name.mkSimple declName_rra0)
        {σ} (br : @& BytesRefImm σ (byteSize $typeId) (alignment $typeId)) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rra1):str]
      opaque $(mkIdent $ Name.mkSimple declName_rra1)
        {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
        (h₁ : i + (byteSize $typeId) ≤ size)
        (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rra2):str]
      opaque $(mkIdent $ Name.mkSimple declName_rra2)
        {σ} {size : @& Nat} (br : @& BytesRefImm σ size (alignment $typeId)) (i : @& Nat)
        (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rru0):str]
      opaque $(mkIdent $ Name.mkSimple declName_rru0)
        {σ} {align : @& Nat} (br : @& BytesRefImm σ (byteSize $typeId) align) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rru1):str]
      opaque $(mkIdent $ Name.mkSimple declName_rru1)
        {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
        (h₁ : i + (byteSize $typeId) ≤ size) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rru2):str]
      opaque $(mkIdent $ Name.mkSimple declName_rru2)
        {σ} {size align : @& Nat} (br : @& BytesRefImm σ size align) (i : @& Nat)
        (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_va0):str]
      opaque $(mkIdent $ Name.mkSimple declName_va0)
        (bv : @& BytesView (byteSize $typeId) (alignment $typeId)) : $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_va1):str]
      opaque $(mkIdent $ Name.mkSimple declName_va1)
        {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
        (h₁ : i + (byteSize $typeId) ≤ size)
        (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) : $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_va2):str]
      opaque $(mkIdent $ Name.mkSimple declName_va2)
        {size : @& Nat} (bv : @& BytesView size (alignment $typeId)) (i : @& Nat)
        (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_vu0):str]
      opaque $(mkIdent $ Name.mkSimple declName_vu0)
         {align : @& Nat} (bv : @& BytesView (byteSize $typeId) align) : $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_vu1):str]
      opaque $(mkIdent $ Name.mkSimple declName_vu1)
        {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
        (h₁ : i + (byteSize $typeId) ≤ size) : $typeId
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_vu2):str]
      opaque $(mkIdent $ Name.mkSimple declName_vu2)
        {size align : @& Nat} (bv : @& BytesView size align) (i : @& Nat)
        (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : $typeId
    ),
    ← `(command|
      instance : ReadBytes $typeId where
        readBytesRef := $(mkIdent $ .mkSimple declName_rra0)
        readBytesRefOff := $(mkIdent $ .mkSimple declName_rra1)
        readBytesRefOffEl := $(mkIdent $ .mkSimple declName_rra2)
        readBytesRefUnal := $(mkIdent $ .mkSimple declName_rru0)
        readBytesRefOffUnal := $(mkIdent $ .mkSimple declName_rru1)
        readBytesRefOffElUnal := $(mkIdent $ .mkSimple declName_rru2)
        readBytesView := $(mkIdent $ .mkSimple declName_va0)
        readBytesViewOff := $(mkIdent $ .mkSimple declName_va1)
        readBytesViewOffEl := $(mkIdent $ .mkSimple declName_va2)
        readBytesViewUnal := $(mkIdent $ .mkSimple declName_vu0)
        readBytesViewOffUnal := $(mkIdent $ .mkSimple declName_vu1)
        readBytesViewOffElUnal := $(mkIdent $ .mkSimple declName_vu2)
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwa0):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwa0)
        {σ} (br : @& BytesRefMut σ (byteSize $typeId) (alignment $typeId))
        (value : @& $typeId) : ST σ Unit
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwa1):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwa1)
        {σ} {size align : @& Nat}
        (br : @& BytesRefMut σ size align) (i : @& Nat) (value : @& $typeId)
        (h₁ : i + (byteSize $typeId) ≤ size)
        (h₂ : ∀ m, ∃ n, align * m + i = (alignment $typeId) * n) :
        ST σ Unit
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwa2):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwa2)
        {σ} {size : @& Nat} (br : @& BytesRefMut σ size (alignment $typeId)) (i : @& Nat)
        (value : @& $typeId) (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ Unit
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwu0):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwu0)
        {σ} {align : @& Nat} (br : @& BytesRefMut σ (byteSize $typeId) align)
        (value : @& $typeId) : ST σ Unit
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwu1):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwu1)
        {σ} {size align : @& Nat} (br : @& BytesRefMut σ size align) (i : @& Nat)
        (value : @& $typeId) (h₁ : i + (byteSize $typeId) ≤ size) : ST σ Unit
    ),
    ← `(command|
      @[extern $(mkStrLit $ "lean_pod_" ++ declName_rwu2):str]
      opaque $(mkIdent $ Name.mkSimple declName_rwu2)
        {σ} {size align : @& Nat} (br : @& BytesRefMut σ size align) (i : @& Nat) (value : @& $typeId)
        (h : i * (byteSize $typeId) + (byteSize $typeId) ≤ size) : ST σ Unit
    ),
    ← `(command|
      instance : WriteBytes $typeId where
        writeBytesRef := $(mkIdent $ .mkSimple declName_rwa0)
        writeBytesRefOff := $(mkIdent $ .mkSimple declName_rwa1)
        writeBytesRefOffEl := $(mkIdent $ .mkSimple declName_rwa2)
        writeBytesRefUnal := $(mkIdent $ .mkSimple declName_rwu0)
        writeBytesRefOffUnal := $(mkIdent $ .mkSimple declName_rwu1)
        writeBytesRefOffElUnal := $(mkIdent $ .mkSimple declName_rwu2)
    )
  ]

#pod_c_rwbytes_instance UInt8
#pod_c_rwbytes_instance UInt16
#pod_c_rwbytes_instance UInt32
#pod_c_rwbytes_instance UInt64
#pod_c_rwbytes_instance USize
#pod_c_rwbytes_instance Float
#pod_c_rwbytes_instance Pod.Float32

instance {size alignment} : GetElem (Pod.BytesView size alignment) Nat UInt8 λ _ i ↦ i < size where
  getElem bv i h := Pod.readBytesViewOff_UInt8 bv i h
    λ m ↦ Exists.intro (alignment * m + i) $ by
      show alignment * m + i = 1 * (alignment * m + i)
      rw [Nat.one_mul (alignment * m + i)]

variable {σ : Type} {offset size : Nat}

def serialize16Le (val : UInt16) (br : BytesRefMut σ size 1)
  (h : offset + 2 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serialize16Be (val : UInt16) (br : BytesRefMut σ size 1)
  (h : offset + 2 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserialize16Le : DeserializationM UInt16 :=
  UInt16.toLittleEndian <$> deserialize UInt16

def deserialize16Be : DeserializationM UInt16 :=
  UInt16.toBigEndian <$> deserialize UInt16

def serialize32Le (val : UInt32) (br : BytesRefMut σ size 1)
  (h : offset + 4 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serialize32Be (val : UInt32) (br : BytesRefMut σ size 1)
  (h : offset + 4 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserialize32Le : DeserializationM UInt32 :=
  UInt32.toLittleEndian <$> deserialize UInt32

def deserialize32Be : DeserializationM UInt32 :=
  UInt32.toBigEndian <$> deserialize UInt32

def serialize64Le (val : UInt64) (br : BytesRefMut σ size 1)
  (h : offset + 8 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serialize64Be (val : UInt64) (br : BytesRefMut σ size 1)
  (h : offset + 8 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserialize64Le : DeserializationM UInt64 :=
  UInt64.toLittleEndian <$> deserialize UInt64

def deserialize64Be : DeserializationM UInt64 :=
  UInt64.toBigEndian <$> deserialize UInt64

def serializeSzLe (val : USize) (br : BytesRefMut σ size 1)
  (h : offset + byteSize USize ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serializeSzBe (val : USize) (br : BytesRefMut σ size 1)
  (h : offset + byteSize USize ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserializeSzLe : DeserializationM USize :=
  USize.toLittleEndian <$> deserialize USize

def deserializeSzBe : DeserializationM USize :=
  USize.toBigEndian <$> deserialize USize

def serializeF32Le (val : Float32) (br : BytesRefMut σ size 1)
  (h : offset + 4 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serializeF32Be (val : Float32) (br : BytesRefMut σ size 1)
  (h : offset + 4 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserializeF32Le : DeserializationM Float32 :=
  Float32.toLittleEndian <$> deserialize Float32

def deserializeF32Be : DeserializationM Float32 :=
  Float32.toBigEndian <$> deserialize Float32

def serializeF64Le (val : Float) (br : BytesRefMut σ size 1)
  (h : offset + 8 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toLittleEndian h

def serializeF64Be (val : Float) (br : BytesRefMut σ size 1)
  (h : offset + 8 ≤ size) : ST σ Unit :=
    br.setOffUnal offset val.toBigEndian h

def deserializeF64Le : DeserializationM Float :=
  Float.toLittleEndian <$> deserialize Float

def deserializeF64Be : DeserializationM Float :=
  Float.toBigEndian <$> deserialize Float
