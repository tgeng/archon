Let(
  t = Def(qn = qn"__unresolved__.Integer") @ "Integer",
  ty = Auto() @ "ε",
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.eff1") @ "eff1",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.usage1") @ "usage1",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = F(vTy = Var(idx = 0) @ "ε", effects = Var(idx = 0), usage = Var(idx = 0)) @ "<eff1> [usage1] Integer",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"