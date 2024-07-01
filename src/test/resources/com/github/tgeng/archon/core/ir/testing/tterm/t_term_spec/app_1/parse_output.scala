TRedex(
  c = TId(id = "f") @ "f",
  elims = List(
    ETerm(v = TId(id = "a") @ "a"),
    ETerm(v = TId(id = "b") @ "b"),
    ETerm(v = TId(id = "c") @ "c"),
    ETerm(v = TId(id = "d") @ "d")
  )
) @ """f a b
  c d"""