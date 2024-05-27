Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.b") @ "b",
    ty = Auto() @ "ε",
    eff = Auto(),
    usage = Auto(),
    body = Redex(
      t = Let(
        t = Def(qn = qn"__unresolved__.a") @ "a",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Redex(
          t = Def(qn = qn"__unresolved__.f") @ "f",
          elims = List(ETerm(v = Var(idx = 0) @ "ε"))
        ) @ "f a"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ "f a b"
  ) @ "ε",
  ty = Auto(),
  eff = Auto(),
  usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.zero") @ "ε") @ "ε",
  body = Let(
    t = Def(qn = qn"__unresolved__.d") @ "d",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Redex(
      t = Let(
        t = Def(qn = qn"__unresolved__.c") @ "c",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Redex(
          t = Def(qn = qn"__unresolved__.g") @ "g",
          elims = List(ETerm(v = Var(idx = 0)))
        ) @ "g c"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ "g c d"
  ) @ "ε"
) @ """f a b
g c d"""