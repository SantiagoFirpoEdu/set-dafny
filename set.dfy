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

  predicate IsSeqUnique(sequence: seq<int>)
  {
    forall i, j :: (0 <= i < |sequence| && 0 <= j < |sequence| && i != j) ==> (sequence[i] != sequence[j])
  }

  ghost predicate Valid()
    reads this
    reads concreteContent
  {
    && (forall i, j :: (0 <= i < |content| && 0 <= j < |content| && i != j) ==> (content[i] != content[j]))
    && concreteContent[..] == content
  }

  method Add(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Contains(x)
    ensures !IsEmpty()
    ensures old(Contains(x)) <==> Size() == old(Size()) && content == old(content)
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
  requires Valid()
  ensures Valid()
  ensures !Contains(x)
  ensures forall a :: a in old(content) && a != x ==> a in content
  ensures forall i, j :: (0 <= i < |content| && 0 <= j < |content| && i != j) ==> (content[i] != content[j])
  modifies this
  modifies this.concreteContent
  ensures old(Contains(x)) ==> old(concreteContent).Length == concreteContent.Length - 1
  ensures old(!Contains(x)) ==> old(concreteContent) == concreteContent
{
  if !Contains(x) {
    return;
  }

  var newContent := new int[concreteContent.Length - 1];
  var i := 0;
  var j := 0;
  var occurences := 0;

  while i < concreteContent.Length
    invariant 0 <= i <= concreteContent.Length
    invariant 0 <= j <= newContent.Length
    invariant forall p :: (0 <= p < j) ==> newContent[p] != x
    invariant forall p :: p in newContent[..j] ==> p in content && p != x
    invariant forall p, q :: (0 <= p < j && 0 <= q < j && p != q) ==> newContent[p] != newContent[q]
    decreases newContent.Length + concreteContent.Length - j - i
    decreases newContent.Length - j
  {
    assert j <= newContent.Length;
    if concreteContent[i] != x {
      newContent[j] := concreteContent[i];
      assert !(exists k :: 0 <= k < concreteContent.Length && k != i && concreteContent[k] == concreteContent[i]);
      j := j + 1;
    }
    else
    {
      occurences := occurences + 1;
    }

    i := i + 1;
  }

  concreteContent := newContent;
  content := newContent[..];

  // assert forall i, j :: (0 <= i < |content| && 0 <= j < |content| && i != j) ==> content[i] != content[j];
}

  function Contains(x: int): bool
    reads this
    reads concreteContent
    requires Valid()
    ensures Valid()
    ensures Contains(x) <==> x in content && exists i :: 0 <= i < concreteContent.Length && concreteContent[i] == x && forall j :: 0 <= j < concreteContent.Length && j != i ==> concreteContent[j] != x
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
    ensures fresh(result)
    ensures forall x :: result.Contains(x) == Contains(x) || other.Contains(x)
  {
    var uniqueCount := concreteContent.Length;
    for i := 0 to other.concreteContent.Length
    {
      if other.concreteContent[i] !in concreteContent[..]
      {
        uniqueCount := uniqueCount + 1;
      }
    }

    var newContent := new int[uniqueCount];
    for i := 0 to concreteContent.Length
    {
      if concreteContent[i] !in other.concreteContent[..]
      {
        newContent[i] := concreteContent[i];
      }
    }
    for i := 0 to other.concreteContent.Length
    {
      if other.concreteContent[i] !in concreteContent[..]
      {
        newContent[i + concreteContent.Length] := other.concreteContent[i];
      }
    }

    result := new IntSet();
    result.concreteContent := newContent;
    result.content := newContent[..];
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