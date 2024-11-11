method Main()
{
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
  s.RemoveIfPresent(2);
  assert s.Size() == 2;
  assert !s.Contains(2);
  assert !s.Contains(3);
  s.RemoveIfPresent(3);
  assert s.Size() == 2;
  assert !s.Contains(2);  
  s.RemoveIfPresent(2);
  assert s.Size() == 2;
  assert !s.Contains(2);
  assert !s.Contains(3);
  s.RemoveIfPresent(1);
  assert s.Size() == 1;
  assert !s.Contains(1);
  assert !s.Contains(2);
  s.RemoveIfPresent(0);
  assert s.Size() == 0;
  assert !s.Contains(0);
  s.Add(0);
  assert s.Size() == 1;
  assert s.Contains(0);
  s.Add(1);
  assert s.Size() == 2;
  assert s.Contains(0);
  assert s.Contains(1);
  s.Add(2);
  assert s.Size() == 3;
  assert s.Contains(0);
  assert s.Contains(1);
  assert s.Contains(2);
}

function Occurences(s: seq<int>, x: int): nat
  ensures Occurences(s, x) <= |s|
{
  if |s| == 0 then 0
  else if s[0] == x then 1 + Occurences(s[1..], x) else Occurences(s[1..], x)
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

  predicate Unique(sequence: seq<int>)
    ensures Unique(sequence) <==> forall i, j :: 0 <= i < |sequence| && 0 <= j < |sequence| && i != j ==> sequence[i] != sequence[j]
  {
    forall i, j :: 0 <= i < |sequence| && 0 <= j < |sequence| && i != j ==> sequence[i] != sequence[j]
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

method RemoveIfPresent(x: int)
  requires Valid()
  ensures Valid()
  ensures !Contains(x)
  modifies this
  ensures forall a :: old(Contains(a)) && a != x <==> Contains(a)
  modifies concreteContent
  ensures old(Contains(x)) <==> fresh(concreteContent)
  ensures old(!Contains(x)) <==> (!fresh(concreteContent) && concreteContent == old(concreteContent))
  ensures forall a :: old(Contains(a)) && a != x ==> Contains(a)
{
  if !Contains(x) {
    assert old(Size()) == Size();
    return;
  }

  assert Unique(concreteContent[..]);

  var newSeq := [];
  assert Unique(newSeq);
  for i := 0 to concreteContent.Length
    invariant Unique(concreteContent[..])
    invariant Unique(newSeq)
    invariant forall a :: a in newSeq <==> a in concreteContent[..i] && a != x
    invariant x !in newSeq
    invariant |newSeq| <= i
    invariant forall a :: a in concreteContent[i..] ==> a !in newSeq
    invariant forall a :: a in concreteContent[..i] && a != x ==> a in newSeq
    invariant old(concreteContent[..]) == concreteContent[..]
    invariant forall a :: old(Contains(a)) && a != x ==> Contains(a)
  {
    if concreteContent[i] != x
    {
      assert concreteContent[i] !in newSeq;
      assert !exists j :: 0 <= j < |newSeq| && newSeq[j] == concreteContent[i];
      newSeq := newSeq + [concreteContent[i]];
      assert old(Contains(concreteContent[i]));
      assert concreteContent[i] in old(content);
      assert concreteContent[i] in newSeq;
      assert x !in newSeq;
    }
    else
    {
      assert !exists j :: 0 <= j < |newSeq| && newSeq[j] == concreteContent[i];
      assert !exists j :: 0 <= j < |newSeq| && newSeq[j] == x;
    }
  }

  var newConcreteContent := new int[|newSeq|];
  assert newConcreteContent.Length == |newSeq|;
  assert allocated(newConcreteContent);
  forall i | 0 <= i < newConcreteContent.Length
  {
    newConcreteContent[i] := newSeq[i];
  }

  assert newConcreteContent[..] == newSeq;

  concreteContent := newConcreteContent;
  content := concreteContent[..];
  assert forall a :: old(Contains(a)) ==> a in old(content);
  assert forall a :: a in old(content) && a != x ==> a in newSeq;
}

  method Union(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures content == old(content) && other.content == old(other.content)
    ensures fresh(result)
    ensures forall x :: x in result.content <==> x in content || x in other.content
  {
    result := new IntSet();
    var newContent := concreteContent[..];
    assert forall x :: x in newContent <==> x in concreteContent[..];

    for i := 0 to |other.concreteContent[..]|
      invariant Unique(newContent)
      invariant forall x :: x in newContent <==> x in concreteContent[..] || x in other.concreteContent[..]
    {
      if other.concreteContent[i] !in newContent
      {
        newContent := newContent + [other.concreteContent[i]];
        assert other.concreteContent[i] in newContent;
      }
    }

    result.concreteContent := new int[|newContent|];
    forall i | 0 <= i < |newContent|
    {
      result.concreteContent[i] := newContent[i];
    }
    
    assert Unique(newContent);
    result.content := result.concreteContent[..];
    assert result.content == result.concreteContent[..];
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
}