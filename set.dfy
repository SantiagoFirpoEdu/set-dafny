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
  ensures forall a :: old(Contains(a)) && a != x ==> Contains(a)
  modifies this
  modifies concreteContent
{
  if !Contains(x) {
    return;
  }

  assert Unique(concreteContent[..]);

  var newSeq := [];
  for i := 0 to concreteContent.Length
    invariant Unique(concreteContent[..])
    invariant forall a :: a in newSeq <==> a in concreteContent[..i] && a != x
    invariant x !in newSeq
    invariant |newSeq| <= i
    invariant forall a, b :: 0 <= a < |newSeq| && 0 <= b < |newSeq| && a != b ==> newSeq[a] != newSeq[b]
    invariant old(concreteContent[..]) == concreteContent[..]
  {
    if concreteContent[i] != x
    {
      newSeq := newSeq + [concreteContent[i]];
    }
  }

  var newConcreteContent := new int[|newSeq|];
  var i := 0;
  while i < newConcreteContent.Length
    modifies newConcreteContent
  {
    newConcreteContent[i] := newSeq[i];
    i := i + 1;
  }

  concreteContent := newConcreteContent;
  content := newConcreteContent[..];
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