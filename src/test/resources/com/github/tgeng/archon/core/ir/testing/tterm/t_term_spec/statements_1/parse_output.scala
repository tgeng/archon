TLet(
  name = "_",
  t = TApp(
    f = TApp(f = TId(id = "f") @ "f", arg = TId(id = "a") @ "a") @ "f a",
    arg = TId(id = "b") @ "b"
  ) @ "f a b",
  ty = TAuto() @ "ε",
  effects = TAuto(),
  usage = TDef(qn = qn"archon.builtin.type.Usage.u0") @ "ε",
  body = TApp(
    f = TApp(f = TId(id = "g") @ "g", arg = TId(id = "c") @ "c") @ "g c",
    arg = TId(id = "d") @ "d"
  ) @ "g c d"
) @ """f a b
g c d"""