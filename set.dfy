//Autores: Henrique Balejos Candaten, Lucas Alves Soares, Miguel Warken, Vitor Caús e Santiago Firpo

method Main()
{
  EmptyStateTest();
  AddTest();
  ContainsTest();
  SizeTest();
  IsEmptyTest();
  RemoveIfPresentTest();
  UnionTest();
  IntersectionTest();
}

method EmptyStateTest()
{
  var s := new IntSet();
  assert s.IsEmpty();
  assert s.Size() == 0;
}

method AddTest()
{
  var s := new IntSet();
  s.Add(0);
  assert s.Size() == 1;
  s.Add(1);
  assert !s.Contains(2);
  assert s.Size() == 2;
  assert s.Contains(1);
  s.Add(2);
  s.Add(2);
  s.Add(2);
  s.Add(2);
  s.Add(2);
  assert s.Size() == 3;
  assert s.Contains(2);
  assert !s.Contains(3);
}

method ContainsTest()
{
  var s := new IntSet();
  s.Add(0);
  s.Add(1);
  s.Add(2);
  assert s.Contains(0);
  assert s.Contains(1);
  assert s.Contains(2);
  assert !s.Contains(3);
}

method SizeTest()
{
  var s := new IntSet();
  s.Add(0);
  s.Add(1);
  s.Add(2);
  assert s.Size() == 3;
}

method IsEmptyTest()
{
  var s := new IntSet();
  assert s.IsEmpty();
  s.Add(0);
  assert !s.IsEmpty();
}

method RemoveIfPresentTest()
{
  var s := new IntSet();
  s.Add(0);
  s.Add(1);
  s.Add(2);
  s.RemoveIfPresent(0);
  assert s.Size() == 2;
  assert !s.Contains(0);
  s.RemoveIfPresent(1);
  s.RemoveIfPresent(1);
  assert s.Size() == 1;
  assert !s.Contains(1);
  s.RemoveIfPresent(2);
  assert s.Size() == 0;
  assert !s.Contains(2);
}

method UnionTest()
{
  var s1 := new IntSet();
  s1.Add(1);
  s1.Add(2);
  var s2 := new IntSet();
  s2.Add(3);
  s2.Add(4);
  s2.Add(4);
  var union := s1.Union(s2);
  assert union.Contains(1);
  assert union.Contains(2);
  assert union.Contains(3);
  assert union.Contains(4);
  assert union.Size() == 4;
  assert forall x :: x in union.content <==> x in s1.content || x in s2.content;
  assert union.content == {1, 2, 3, 4};
}

method IntersectionTest()
{
  var s1 := new IntSet();
  s1.Add(2);
  s1.Add(3);
  s1.Add(4);
  s1.Add(5);
  assert s1.content == {2, 3, 4, 5};
  var s2 := new IntSet();
  s2.Add(2);
  s2.Add(3);
  s2.Add(4);
  assert s2.content == {2, 3, 4};

  var intersection := s1.Intersection(s2);
  assert intersection.content == {2, 3, 4};
  assert intersection.Size() == 3;
}

ghost function AsSet(sequence: seq<int>): set<int>
  requires Unique(sequence)
{
  set x | x in sequence
}

lemma UniqueCountEqualsSetCardinality(sequence: seq<int>)
  requires Unique(sequence)
  ensures |AsSet(sequence)| == |sequence|
{
  if sequence != []
  {
    assert AsSet(sequence) == {sequence[0]} + AsSet(sequence[1..]);
    UniqueCountEqualsSetCardinality(sequence[1..]);
  }
  else
  {
    assert |AsSet(sequence)| == |sequence|;
  }
}

predicate Unique(sequence: seq<int>)
  ensures Unique(sequence) <==> forall i, j :: 0 <= i < |sequence| && 0 <= j < |sequence| && i != j ==> sequence[i] != sequence[j]
  ensures Unique(sequence) ==> forall x :: x in sequence <==> x in set x | x in sequence
{
  forall i, j :: 0 <= i < |sequence| && 0 <= j < |sequence| && i != j ==> sequence[i] != sequence[j]
}

class IntSet
{
  ghost var content: set<int>
  var concreteContent: array<int>

  constructor ()
    ensures Valid()
    ensures IsEmpty()
    ensures Size() == 0
    ensures content == {}
    ensures forall x :: !Contains(x)
    ensures fresh(concreteContent)
    ensures allocated(concreteContent)
  {
    concreteContent := new int[0];
    content := {};
  }

  ghost predicate Valid()
    reads this
    reads concreteContent
  {
    && Unique(concreteContent[..])
    && (forall x :: x in content <==> x in concreteContent[..])
    && (|content| == concreteContent.Length)
  }

  method Add(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Contains(x)
    ensures !IsEmpty()
    ensures old(Contains(x)) <==> Size() == old(Size()) && content == old(content)
    ensures !old(Contains(x)) <==> Size() == old(Size()) + 1
    ensures content == old(content) + {x}
  {
    if (x in concreteContent[..])
    {
      assert Contains(x);
      assert !IsEmpty();
      return;
    }

    var newContent := concreteContent[..];
    
    newContent := newContent + [x];
    assert Unique(newContent);

    var newConcreteContent := new int[|newContent|];
    content := {};

    for i := 0 to |newContent|
      invariant forall a :: a in newContent[..i] <==> a in content
      invariant |newContent[..i]| == |content|
    {
      content := content + {newContent[i]};
    }

    forall i | 0 <= i < newConcreteContent.Length
    {
      newConcreteContent[i] := newContent[i];
    }

    assert newContent == newConcreteContent[..];
    assert x in newContent;
    assert x in newConcreteContent[..];
    assert Unique(newContent);
    assert Unique(newConcreteContent[..]);

    concreteContent := newConcreteContent;
    assert Unique(concreteContent[..]);
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
    ensures IsEmpty() == (content == {})
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

    var newConcreteContent := new int[|newSeq|];
    assert newConcreteContent.Length == |newSeq|;
    assert allocated(newConcreteContent);
    forall i | 0 <= i < newConcreteContent.Length
    {
      newConcreteContent[i] := newSeq[i];
    }

    assert newConcreteContent[..] == newSeq;

    concreteContent := newConcreteContent;

    content := content - {x};

    assert forall a :: old(Contains(a)) ==> a in old(content);
    assert forall a :: a in old(content) && a != x ==> a in newSeq;
  }

  method Union(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures content == old(content)
    ensures other.content == old(other.content)
    ensures fresh(result)
    ensures result.Valid()
    ensures result.content == content + other.content
  {
    result := new IntSet();
    var newContent := concreteContent[..];
    assert |newContent| == concreteContent.Length;
    assert newContent == concreteContent[..];

    assert forall x :: x in newContent <==> x in concreteContent[..];

    for i := 0 to |other.concreteContent[..]|
      invariant Unique(newContent)
      invariant forall j :: 0 <= j < i ==> other.concreteContent[j] in newContent
      invariant forall j :: 0 <= j < concreteContent.Length ==> concreteContent[j] in newContent
      invariant forall j :: 0 <= j < |newContent| ==> newContent[j] in other.concreteContent[..] || newContent[j] in concreteContent[..]
      invariant |newContent| >= concreteContent.Length
      invariant forall x :: x in newContent[concreteContent.Length..] ==> x in other.concreteContent[..]
      invariant newContent[..concreteContent.Length] == concreteContent[..]
      invariant forall x :: x in other.concreteContent[..i] && x !in concreteContent[..] <==> x in newContent[concreteContent.Length..]
      invariant |newContent| == concreteContent.Length + |newContent[concreteContent.Length..]|
      invariant forall x :: x in newContent[concreteContent.Length..] <==> x in other.concreteContent[..i] && x !in concreteContent[..]
    {
      if other.concreteContent[i] !in newContent
      {
        newContent := newContent + [other.concreteContent[i]];
      }
    }

    result.concreteContent := new int[|newContent|];
    forall i | 0 <= i < |newContent| {
      result.concreteContent[i] := newContent[i];
    }

    assert result.concreteContent[..] == newContent;
    assert Unique(result.concreteContent[..]);
    assert forall x :: x in result.concreteContent[..] ==> x in newContent;


    result.content := set x | x in newContent;
    assert forall x :: x in result.content <==> (exists i :: 0 <= i < |newContent| && newContent[i] == x && (!exists j :: 0 <= j < |newContent| && j != i && newContent[j] == x));
    UniqueCountEqualsSetCardinality(newContent);
  }

  method Intersection(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures content == old(content)
    ensures other.content == old(other.content)
    ensures fresh(result)
    ensures result.Valid()
    ensures result.content == content * other.content
  {
    result := new IntSet();
    var newContent := [];

    for i := 0 to concreteContent.Length
      invariant Unique(newContent)
      invariant Valid() && other.Valid()
      invariant forall x :: x in newContent <==> (x in concreteContent[..i] && x in other.concreteContent[..])
    {
      if concreteContent[i] in other.concreteContent[..]
      {
        newContent := newContent + [concreteContent[i]];
      }
    }

    result.concreteContent := new int[|newContent|];
    forall i | 0 <= i < |newContent|
    {
      result.concreteContent[i] := newContent[i];
    }

    assert result.concreteContent[..] == newContent;
    assert forall x :: x in result.concreteContent[..] <==> x in newContent;

    result.content := set x | x in newContent;
    UniqueCountEqualsSetCardinality(newContent);
    assert |newContent| == |result.content|;
  }
}