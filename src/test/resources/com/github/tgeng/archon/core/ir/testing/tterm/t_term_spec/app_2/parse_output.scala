TApp(
  f = TApp(
    f = TId(id = "f") @ "f",
    arg = TApp(
      f = TApp(f = TId(id = "g") @ "g", arg = TId(id = "a") @ "a") @ "g a",
      arg = TId(id = "b") @ "b"
    ) @ "g a b"
  ) @ """f
  (g a b""",
  arg = TApp(
    f = TApp(f = TId(id = "h") @ "h", arg = TId(id = "c") @ "c") @ "h c",
    arg = TId(id = "d") @ "d"
  ) @ "h c d"
) @ """f
  (g a b)
  (h c d"""