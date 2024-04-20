Let(
  t = Return(
    v = Thunk(c = Def(qn = qn"__unresolved__.abc") @ "abc") @ "thunk abc",
    usage = Auto() @ "ε"
  ) @ "thunk abc",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Force(v = Var(idx = 0) @ "ε") @ "force (thunk abc)"
) @ "ε"