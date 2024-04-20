TApp(
  f = TApp(
    f = TApp(
      f = TApp(f = TId(id = "f") @ "f", arg = TId(id = "a") @ "a") @ "f a",
      arg = TId(id = "b") @ "b"
    ) @ "f a b",
    arg = TId(id = "c") @ "c"
  ) @ """f a b
  c""",
  arg = TId(id = "d") @ "d"
) @ """f a b
  c d"""