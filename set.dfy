method Main()
{
  // var s := new IntSet();
  // assert s.IsEmpty() == true;
  // assert s.Size() == 0;
  // s.Add(0);
  // assert s.Size() == 1;
  // s.Add(1);
  // assert !s.Contains(2);
  // assert s.Size() == 2;
  // assert s.Contains(1);
  // s.Add(2);
  // s.Add(2);
  // s.Add(2);
  // s.Add(2);
  // s.Add(2);
  // assert s.Size() == 3;
  // assert s.Contains(2);
  // assert !s.Contains(3);
  // s.RemoveIfPresent(2);
  // assert s.Size() == 2;
  // assert !s.Contains(2);
  // assert !s.Contains(3);
  // s.RemoveIfPresent(3);
  // assert s.Size() == 2;
  // assert !s.Contains(2);  
  // s.RemoveIfPresent(2);
  // assert s.Size() == 2;
  // assert !s.Contains(2);
  // assert !s.Contains(3);
  // s.RemoveIfPresent(1);
  // assert s.Size() == 1;
  // assert !s.Contains(1);
  // assert !s.Contains(2);
  // s.RemoveIfPresent(0);
  // assert s.Size() == 0;
  // assert !s.Contains(0);
  // s.Add(0);
  // assert s.Size() == 1;
  // assert s.Contains(0);
  // s.Add(1);
  // assert s.Size() == 2;
  // assert s.Contains(0);
  // assert s.Contains(1);
  // s.Add(2);
  // assert s.Size() == 3;
  // assert s.Contains(0);
  // assert s.Contains(1);
  // assert s.Contains(2);
  // var s2 := new IntSet();
  // s2.Add(9);
  // s2.Add(8);
  // s2.Add(7);
  // s2.Add(6);
  // s2.Add(5);
  var s3 := new IntSet();
  s3.Add(1);
  s3.Add(2);
  var s4 := new IntSet();
  s4.Add(3);
  s4.Add(4);
  var union := s3.Union(s4);
  assert union.Contains(1);
  assert union.Contains(2);
  assert union.Contains(3);
  assert union.Contains(4);
  assert union.Size() == 4;
  assert forall x :: x in union.content <==> x in s3.content || x in s4.content;
}

function Occurences(s: seq<int>, x: int): nat
  ensures Occurences(s, x) <= |s|
{
  if |s| == 0 then 0
  else if s[0] == x then 1 + Occurences(s[1..], x) else Occurences(s[1..], x)
}

function UniqueElements(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[0] !in s[1..] then [s[0]] + UniqueElements(s[1..]) else UniqueElements(s[1..])
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
    ensures fresh(concreteContent)
    ensures allocated(concreteContent)
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
  ensures old(Contains(x)) <==> fresh(concreteContent)
  ensures old(!Contains(x)) <==> concreteContent == old(concreteContent)
  ensures forall a :: old(Contains(a)) && a != x ==> Contains(a)
  ensures !old(Contains(x)) <==> Size() == old(Size()) && content == old(content)
  ensures old(Contains(x)) <==> Size() == old(Size()) - 1
{
  if !Contains(x)
  {
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
    invariant x in concreteContent[..i] ==> |newSeq| == i - 1
    invariant x !in concreteContent[..i] ==> |newSeq| == i
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
      assert !exists j :: 0 <= j < concreteContent.Length && j != i && concreteContent[j] == x;
    }
  }

  assert |newSeq| == |content| - 1;
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
    ensures result.Valid()
    ensures forall x :: result.Contains(x) <==> Contains(x) || other.Contains(x)
    ensures result.content == UniqueElements(content + other.content)
    ensures result.Size() == |UniqueElements(content + other.content)|
  {
    result := new IntSet();
    var newContent := concreteContent[..];
    assert |newContent| == concreteContent.Length;
    assert newContent == concreteContent[..];
    assert UniqueElements(concreteContent[..]) == UniqueElements(newContent);

    assert forall x :: x in newContent <==> x in concreteContent[..];

    for i := 0 to |other.concreteContent[..]|
      invariant Unique(newContent)
      invariant forall j :: 0 <= j < i ==> other.concreteContent[j] in newContent
      invariant forall j :: 0 <= j < concreteContent.Length ==> concreteContent[j] in newContent
      invariant forall j :: 0 <= j < |newContent| ==> newContent[j] in other.concreteContent[..] || newContent[j] in concreteContent[..]
    {
      if other.concreteContent[i] !in newContent
      {
        newContent := newContent + [other.concreteContent[i]];
        assert other.concreteContent[i] in newContent;
        assert (other.concreteContent[i] in other.concreteContent[..]) <==> (other.concreteContent[i] in newContent[..]);
      }
    }

    result.concreteContent := new int[|newContent|];
    forall i | 0 <= i < |newContent|
    {
      result.concreteContent[i] := newContent[i];
    }

    assert result.concreteContent[..] == newContent;

    result.content := result.concreteContent[..];
  }

  method Intersection(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures content == old(content) && other.content == old(other.content)
    ensures fresh(result)
    ensures result.Valid()
    ensures forall x :: result.Contains(x) <==> Contains(x) && other.Contains(x)
  {
    result := new IntSet();
    var newContent := [];

    for i := 0 to |other.concreteContent[..]|
      invariant old(concreteContent[..]) == concreteContent[..]
      invariant old(other.concreteContent[..]) == other.concreteContent[..]
      invariant Unique(concreteContent[..]) && Unique(other.concreteContent[..])
      invariant forall j :: 0 <= j < |newContent| ==> newContent[j] in other.concreteContent[..] && newContent[j] in concreteContent[..]
    {
      if other.concreteContent[i] in concreteContent[..]
      {
        newContent := newContent + [other.concreteContent[i]];
      }
    }

    assert forall j :: 0 <= j < |newContent| ==> newContent[j] in other.concreteContent[..] && newContent[j] in concreteContent[..];

    result.concreteContent := new int[|newContent|];
    forall i | 0 <= i < |newContent|
    {
      result.concreteContent[i] := newContent[i];
    }

    assert result.concreteContent[..] == newContent;
    assert forall x :: x in result.concreteContent[..] ==> x in newContent;

    result.content := result.concreteContent[..];
    assert result.content == result.concreteContent[..];
  }
}