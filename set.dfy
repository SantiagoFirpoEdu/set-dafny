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
  ghost var contents: seq<int>
  ghost var size: nat

  constructor ()
    ensures Valid()
  {
    contents := [];
    size := 0;
  }

  ghost predicate Valid()
    reads this
  {
    && (forall x :: x in contents ==> !(exists y :: y in contents && x != y))
    && size == |contents|
    && concreteContents[..] == contents
  }

  method Add(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Contains(x)
  {
    if (x in concreteContents[..])
    {
      return;
    }
    contents := contents + [x];
    size := size + 1;
    contents := concreteContents[..];
  }

  function Size(): nat
    reads this
    ensures Size() == size
  {
    concreteContents.Length
  } 

  function IsEmpty(): bool
    reads this
    ensures IsEmpty() == (size == 0)
  {
    concreteContents.Length == 0
  }

  method Union(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures forall x :: result.Contains(x) == Contains(x) || other.Contains(x)
  {
    var newContentsontents := concreteContents[..] + other.concreteContents[..];
    result.contents := newContentsontents;
    result := new IntSet();
    result.contents := newContentsontents;
  }

  method Intersection(other: IntSet) returns (result: IntSet)
    requires Valid() && other.Valid()
    ensures Valid() && other.Valid()
    ensures forall x :: result.Contains(x) == Contains(x) && other.Contains(x)
  {
    result := new IntSet();
    var newContents: array<int> := new int[0];
    for i := 0 to |concreteContents[..]|
      invariant forall x :: x in newContents[..] ==> !(exists y :: y in concreteContents[..] && x != y)
    {
      if (concreteContents[i] in other.concreteContents[..])
      {
        newContents[newContents.Length] := concreteContents[i];
      }
    }

    result.concreteContents := newContents;
  }

  method RemoveIfPresent(x: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(this).Contains(x) ==> !Contains(x)
    ensures !Contains(x) ==> contents == old(contents)
  {
    //Do something lol
    size := size - 1;
    contents := concreteContents[..];
  }

  function Contains(x: int): bool
    reads this
    requires Valid()
    ensures Valid()
    ensures Contains(x) ==> x in contents
    ensures !Contains(x) ==> x !in contents
  {
    x in concreteContents[..]
  }
  
  var concreteContents: array<int>
}