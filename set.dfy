method Main() {
  var s := new IntSet();
  s.Add(1);
  s.Add(2);
  s.Add(3);
  s.Add(4);
  s.Add(5);
  assert s.Size() == 5;
  assert s.IsEmpty() == false;
  var emptySet := new IntSet();
  var s2 := s.Union(emptySet);
  assert s2.Size() == 5;
  assert s2.IsEmpty() == false;
  var s3 := s2.Intersection(emptySet);
  assert s3.Size() == 0;
  assert s3.IsEmpty() == true;
}

class IntSet {
  ghost var content: seq<int>
  ghost var size: nat
  
  var concreteContent: array<int>
  var concreteSize: nat

  constructor ()
    ensures Valid()
  {
    concreteContent := new int[0];
    concreteSize := 0;
    content := [];
    size := 0;
  }

  ghost predicate Valid()
    reads this
    reads concreteContent
  {
    && (forall i, j :: (0 <= i < |content| && 0 <= j < |content| && i != j) ==> (content[i] != content[j]))
    && size == |content|
    && size == concreteSize
    && concreteContent[..] == content
  }

  method Add(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Contains(x)
  {
    if (x in concreteContent[..])
    {
      return;
    }

    var newContent := new int[concreteSize + 1];
    forall i | 0 <= i < concreteSize {
      newContent[i] := concreteContent[i];
    }
    
    newContent[concreteSize] := x;

    concreteContent := newContent;
    concreteSize := concreteContent.Length;
    content := concreteContent[..];
    size := |content|;
  }

  method RemoveIfPresent(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures !Contains(x)
  {

    if !Contains(x)
    {
      return;
    }

    var newArr := new int[concreteSize - 1];
    var j := 0;

    for i := 0 to concreteSize - 1
      invariant 0 <= j < concreteSize - 1
      invariant 0 <= j <= i < concreteSize
      invariant forall k :: 0 <= k < j ==> newArr[k] != x
     {
        if concreteContent[i] != x {
            newArr[j] := concreteContent[i];
            j := j + 1;
        }
    }

    concreteContent := newArr;
    concreteSize := concreteSize - 1;

    content := concreteContent[..];
    size := size - 1;
  }

  function Contains(x: int): bool
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures Contains(x) ==> x in content && !IsEmpty()
    ensures !Contains(x) ==> x !in content
  {
    x in concreteContent[..]
  }

  function Size(): nat
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures Size() == size
  {
    concreteSize
  } 

  function IsEmpty(): bool
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures IsEmpty() == (size == 0)
  {
    concreteSize == 0
  }

  method Union(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures forall x :: result.Contains(x) == Contains(x) || other.Contains(x)
  {
    var newContent := concreteContent[..] + other.concreteContent[..];
    result.content := newContent;
    result := new IntSet();
    result.content := newContent;
  }

  method Intersection(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures forall x :: result.Contains(x) == Contains(x) && other.Contains(x)
  {
    result := new IntSet();
    var newContent: array<int> := new int[0];
    for i := 0 to |concreteContent[..]|
      invariant forall x :: x in newContent[..] ==> !(exists y :: y in concreteContent[..] && x != y)
    {
      if (concreteContent[i] in other.concreteContent[..])
      {
        // newContent[newContent.Length] := concreteContent[i];
      }
    }

    result.concreteContent := newContent;
  }

  method RemoveElementManual(sequence: seq<int>, elem: int) returns (newSeq: seq<int>)
  {
      newSeq := [];
      for i := 0 to |sequence| {
          if sequence[i] != elem {
              newSeq := newSeq + [sequence[i]];
          }
      }
  }

}