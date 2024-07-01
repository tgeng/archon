TRedex(
  c = TId(id = "f") @ "f",
  elims = List(
    ETerm(
      v = TRedex(
        c = TId(id = "g") @ "g",
        elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
      ) @ "g a b"
    ),
    ETerm(
      v = TRedex(
        c = TId(id = "h") @ "h",
        elims = List(ETerm(v = TId(id = "c") @ "c"), ETerm(v = TId(id = "d") @ "d"))
      ) @ "h c d"
    )
  )
) @ """f
  (g a b)
  (h c d)"""