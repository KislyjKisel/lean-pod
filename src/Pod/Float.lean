module

import Alloy.C
public import Pod.UInt

open scoped Alloy.C

alloy c include
  <stdlib.h>
  <math.h>
  <lean/lean.h>

public section

namespace Pod

namespace Float32

abbrev inf : Float32 := .ofBits 0x7F800000
abbrev negInf : Float32 := .ofBits 0xFF800000
abbrev pi : Float32 := .ofBits 0x40490FDB

@[expose, inline]
def isUnordered (x y : Float32) : Bool :=
  x.isNaN || y.isNaN

@[expose, inline]
def bswap : Float32 → Float32 :=
  Float32.ofBits ∘ UInt32.bswap ∘ Float32.toBits

@[expose, inline]
def toLittleEndian : Float32 → Float32 :=
  Float32.ofBits ∘ UInt32.toLittleEndian ∘ Float32.toBits

@[expose, inline]
def toBigEndian : Float32 → Float32 :=
  Float32.ofBits ∘ UInt32.toBigEndian ∘ Float32.toBits

alloy c extern def ofString? (s : @& String) : Option Float32 := {
  char* retEnd = NULL;
  const char* cstr = lean_string_cstr(s);
  const char* cstrEnd = cstr + lean_string_size(s) - 1;
  float x = strtof(cstr, &retEnd);
  if (retEnd != cstrEnd) {
    return lean_box(0);
  }
  lean_object* result = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(result, 0, lean_box_float32(x));
  return result;
}

@[expose, inline]
def ofSlice? (s : @& String.Slice) : Option Float32 :=
  ofString? s.toString

alloy c extern def isNormal (x : Float32) : Bool := {
  return isnormal(x);
}

end Float32

namespace Float

abbrev inf : Float := .ofBits 0x7FF0000000000000
abbrev negInf : Float := .ofBits 0xFFF0000000000000
abbrev pi : Float := .ofBits 0x400921FB54442D18

@[expose, inline]
def isUnordered (x y : Float) : Bool :=
  x.isNaN || y.isNaN

@[expose, inline]
def bswap : Float → Float :=
  Float.ofBits ∘ UInt64.bswap ∘ Float.toBits

@[expose, inline]
def toLittleEndian : Float → Float :=
  Float.ofBits ∘ UInt64.toLittleEndian ∘ Float.toBits

@[expose, inline]
def toBigEndian : Float → Float :=
  Float.ofBits ∘ UInt64.toBigEndian ∘ Float.toBits

alloy c extern def ofString? (s : @& String) : Option Float := {
  char* retEnd = NULL;
  const char* cstr = lean_string_cstr(s);
  const char* cstrEnd = cstr + lean_string_size(s) - 1;
  double x = strtod(cstr, &retEnd);
  if (retEnd != cstrEnd) {
    return lean_box(0);
  }
  lean_object* result = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(result, 0, lean_box_float(x));
  return result;
}

@[expose, inline]
def ofSlice? (s : @& String.Slice) : Option Float :=
  ofString? s.toString

alloy c extern def isNormal (x : Float) : Bool := {
  return isnormal(x);
}

end Float
