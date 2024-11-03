method Main() {
  var s := new IntSet();
  assert s.IsEmpty() == true;
  assert s.Size() == 0;
  s.Add(0);
  assert s.Size() == 1;
  s.Add(1);
  assert !s.Contains(2);
  assert s.Size() == 2;
  assert s.Contains(1);
  s.Add(2);
  assert s.Size() == 3;
  assert s.Contains(2);
  assert !s.Contains(3);
}

class IntSet {
  ghost var content: seq<int>
  
  var concreteContent: array<int>

  constructor ()
    ensures Valid()
    ensures IsEmpty()
    ensures Size() == 0
    ensures content == []
    ensures forall x :: !Contains(x)
  {
    concreteContent := new int[0];
    content := [];
  }

  predicate IsValidIndex(sequence: seq<int>, index: int)
  {
    0 <= index < |sequence|
  }

  predicate IsValidIndexForArray(sequence: array<int>, index: int)
  {
    0 <= index < sequence.Length
  }

  predicate IsArrayUnique(sequence: array<int>)
    reads sequence
  {
    forall i, j :: (0 <= i < sequence.Length && 0 <= j < sequence.Length && i != j) ==> (sequence[i] != sequence[j])
  }

  predicate IsSeqUnique(sequence: seq<int>)
  {
    forall i, j :: (0 <= i < |sequence| && 0 <= j < |sequence| && i != j) ==> (sequence[i] != sequence[j])
  }

  ghost predicate Valid()
    reads this
    reads concreteContent
  {
    && IsArrayUnique(concreteContent)
    && IsSeqUnique(content)
    && concreteContent[..] == content
  }

  method Add(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Contains(x)
    ensures !IsEmpty()
    ensures Size() > 0
    ensures old(Contains(x)) <==> Size() == old(Size())
    ensures !old(Contains(x)) <==> Size() == old(Size()) + 1 && content == old(content) + [x]
  {
    if (x in concreteContent[..])
    {
      assert Contains(x);
      assert !IsEmpty();
      return;
    }

    var newContent := new int[concreteContent.Length + 1];
    forall i | 0 <= i < concreteContent.Length
    {
      newContent[i] := concreteContent[i];
    }
    
    newContent[concreteContent.Length] := x;

    concreteContent := newContent;
    content := newContent[..];
    assert Contains(x);
    assert !IsEmpty();
  }

  method RemoveIfPresent(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures !Contains(x)
  {
    if !Contains(x)
    {
      assert IsArrayUnique(concreteContent);
      assert !Contains(x);
      return;
    }

    assert Contains(x);

    var newArr := new int[concreteContent.Length - 1];
    forall j | 0 <= j < newArr.Length
    {
      newArr[j] := 0;
    }
    var i := 0;
    var j := 0;
    assert IsArrayUnique(concreteContent);
    assert IsSeqUnique(content);

    //Manually remove the element
    while (i < concreteContent.Length && j < newArr.Length)
      invariant 0 <= j <= i <= concreteContent.Length
      invariant 0 <= j <= newArr.Length
      invariant x !in newArr[..j]
      invariant !exists k :: k in newArr[..j] && k !in concreteContent[..]
      invariant forall k :: 0 <= k < j ==> newArr[k] != x
    {
      if (concreteContent[i] != x)
      {
        newArr[j] := concreteContent[i];
        j := j + 1;
      }

      i := i + 1;
    }


    content := newArr[..];
    concreteContent := newArr;
  }

  function Contains(x: int): bool
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures Contains(x) <==> x in content
  {
    x in concreteContent[..]
  }

  function Size(): nat
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures Size() == |content|
  {
    concreteContent.Length
  } 

  function IsEmpty(): bool
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures IsEmpty() == (Size() == 0)
    ensures IsEmpty() == (content == [])
  {
    concreteContent.Length == 0
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
      for i := 0 to |sequence|
      {
          if sequence[i] != elem
          {
              newSeq := newSeq + [sequence[i]];
          }
      }
  }
}