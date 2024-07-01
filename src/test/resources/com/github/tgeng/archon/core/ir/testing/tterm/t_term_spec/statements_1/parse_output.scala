TLet(
  name = "_",
  t = TRedex(
    c = TId(id = "f") @ "f",
    elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
  ) @ "f a b",
  ty = TAuto() @ "ε",
  effects = TAuto(),
  usage = TDef(qn = qn"archon.builtin.type.Usage.u0") @ "ε",
  body = TRedex(
    c = TId(id = "g") @ "g",
    elims = List(ETerm(v = TId(id = "c") @ "c"), ETerm(v = TId(id = "d") @ "d"))
  ) @ "g c d"
) @ """f a b
g c d"""