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

  assert exists i :: (0 <= i < concreteContent.Length && concreteContent[i] == x) && forall j :: (0 <= j < concreteContent.Length && j != i ==> concreteContent[j] != x);

  var newContent := new int[concreteContent.Length - 1];
  var i := 0;
  var j := 0;

  while j < newContent.Length
    invariant 0 <= i <= concreteContent.Length
    invariant 0 <= j <= newContent.Length
    invariant concreteContent == old(concreteContent)
    invariant content == old(content)
    invariant x !in newContent[..j]
    invariant forall a :: 0 <= a < i && concreteContent[a] != x ==> exists b :: 0 <= b < j && newContent[b] == concreteContent[a] && !exists c :: 0 <= c < j && c != b && newContent[c] == newContent[b]
    decreases concreteContent.Length - i
  {
    assert i != concreteContent.Length;
    if concreteContent[i] != x {
      assert j < concreteContent.Length;
      newContent[j] := concreteContent[i];
      assert concreteContent[i] in newContent[..j + 1];
      assert newContent[j] != x;

      j := j + 1;
    }

    i := i + 1;
  }
  
  assert forall a, b :: (0 <= a < j && 0 <= b < j && a != b) ==> (newContent[a] != newContent[b]);

  assert x !in newContent[..];
  content := newContent[..];
  concreteContent := newContent;
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