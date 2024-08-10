import Specs
import Pod

open Specs Matchers

namespace Pod.Tests

def deque :=
  describe "Deque" do
    it "size empty = 0" do
      isEqual (Deque.empty : Deque Nat).size 0
    it "size (singleton 42) = 1" do
      isEqual (Deque.singleton 42).size 1
    it "size (mkEmpty 100) = 0" do
      isEqual (Deque.mkEmpty 100 : Deque Nat).size 0
    it "size (empty.pushBack 42) = 1" do
      isEqual (Deque.empty.pushBack 42).size 1
    it "size ((empty.pushFront 42).pushFront 12) = 2" do
      isEqual (Deque.empty.pushFront 42 |>.pushFront 12).size 2
    it "isEmpty empty" do
      isTrue (Deque.empty : Deque Nat).isEmpty
    it "isEmpty (ofList [])" do
      isTrue (Deque.ofList [] : Deque Nat).isEmpty
    it "isEmpty (ofArray #[])" do
      isTrue (Deque.ofArray #[] : Deque Nat).isEmpty
    it "¬ isEmpty (empty.pushBack true)" do
      isTrue <| not (Deque.empty.pushBack true).isEmpty
    it "¬ isEmpty (ofList [1])" do
      isTrue <| not (Deque.ofList [1]).isEmpty
    it "toArray∘ofArray [true]" do
      isEqual (Deque.ofArray #[true]).toArray #[true]
    it "toList∘ofList ['x']" do
      isEqual (Deque.ofList ['x']).toList ['x']
    it "toArray∘ofList [1,2,3]" do
      isEqual (Deque.ofList [1, 2, 3]).toArray #[1, 2, 3]
    it "toArray∘ofList []" do
      isEqual (Deque.ofList ([] : List Nat)).toArray #[]
    it "toList∘ofArray ['a','b','c']" do
      isEqual (Deque.ofArray #["a", "b", "c"]).toList ["a", "b", "c"]
    it "toList∘ofArray #[]" do
      isEqual (Deque.ofArray (#[] : Array Nat)).toList []
    it "(replicate 5 'w').toArray = Array.mkArray 5 'w'" do
      isEqual (Deque.replicate 5 'w').toArray (Array.mkArray 5 'w')
    it "(empty.pushBack 1).peekBack _ = 1" do
      isEqual (if h: _ then (Deque.empty.pushBack 1).peekBack h else 0) 1
    it "(empty.pushFront 'x' |>.pushBack 'y').peekFront _ = 'x'" do
      isEqual (if h: _ then (Deque.empty.pushFront 'x' |>.pushBack 'y').peekFront h else '#') 'x'
    it "(empty.pushFront 'y' |>.pushBack 'z' |>.pushFront 'x').toList = ['x','y','z']" do
      isEqual (Deque.empty.pushFront 'y' |>.pushBack 'z' |>.pushFront 'x').toList ['x','y','z']
    it "(ofList ['x','y','z'] |>.get! 1) = 'y'" do
      isEqual (Deque.ofList ['x','y','z'] |>.get! 1) 'y'

def all :=
  describe "Pod" do
    deque

end Pod.Tests

def main := runCli Pod.Tests.deque
