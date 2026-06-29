module

import LSpec
import Pod

open LSpec

namespace Pod.Tests

def float32 := group "Float32"
  <| test "Float32.ofSlice? 1.24" (Pod.Float32.ofSlice? "1.24".toSlice == some 1.24)
  <| test "Float32.ofSlice? -0.1" (Pod.Float32.ofSlice? "-0.1".toSlice == some (-0.1))
  <| test "Float32.ofSlice? 1.4x" (Pod.Float32.ofSlice? "1.4x".toSlice == none)
  <| test "toLittleEndian bswap = toBigEndian bswap bswap"
    ((3.14 |> Pod.Float32.toLittleEndian |> Pod.Float32.bswap) == (3.14 |> Pod.Float32.toBigEndian |> Pod.Float32.bswap |> Pod.Float32.bswap))
  <| test "isNormal 1" (Pod.Float32.isNormal 1)
  <| test "¬ isNormal 0" (Pod.Float32.isNormal 0).not
  <| test "¬ isNormal ∞" (Pod.Float32.isNormal Pod.Float32.inf).not

def float := group "Float"
  <| test "Float.ofSlice? 1.24" (Pod.Float.ofSlice? "1.24".toSlice == some 1.24)
  <| test "Float.ofSlice? -0.1" (Pod.Float.ofSlice? "-0.1".toSlice == some (-0.1))
  <| test "Float.ofSlice? 1.4x" (Pod.Float.ofSlice? "1.4x".toSlice == none)
  <| test "toLittleEndian bswap = toBigEndian bswap bswap"
    ((3.14 |> Pod.Float.toLittleEndian |> Pod.Float.bswap) == (3.14 |> Pod.Float.toBigEndian |> Pod.Float.bswap |> Pod.Float.bswap))
  <| test "isNormal 1" (Pod.Float.isNormal 1)
  <| test "¬ isNormal 0" (Pod.Float.isNormal 0).not
  <| test "¬ isNormal ∞" (Pod.Float.isNormal Pod.Float.inf).not

end Pod.Tests

public def main : List String → IO UInt32 :=
  lspecIO ∘ Std.HashMap.ofList ∘ List.map (Prod.map id List.singleton) <| [
    ("float32", Pod.Tests.float32),
    ("float", Pod.Tests.float),
  ]
