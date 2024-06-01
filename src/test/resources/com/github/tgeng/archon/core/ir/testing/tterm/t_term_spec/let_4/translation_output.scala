Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.getA1") @ "getA1",
    tBinding = Binding(
      ty = Auto() @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
      usage = Collapse(
        cTm = Return(v = Auto(), usage = Auto() @ "ε") @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2"""
      ) @ "ε"
    ) @ "a1",
    eff = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.getA2") @ "getA2",
      tBinding = Binding(
        ty = Auto() @ """let a2 = getA2
  plus a1 a2""",
        usage = Collapse(
          cTm = Return(v = Auto(), usage = Auto()) @ """let a2 = getA2
  plus a1 a2"""
        )
      ) @ "a2",
      eff = Auto(),
      body = Let(
        t = Return(v = Var(idx = 0) @ "a2", usage = Auto()) @ "a2",
        tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
        eff = Auto(),
        body = Redex(
          t = Let(
            t = Return(v = Var(idx = 2) @ "a1", usage = Auto()) @ "a1",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.plus") @ "plus",
              elims = List(ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "plus a1"
          ) @ "ε",
          elims = List(ETerm(v = Var(idx = 0)))
        ) @ "plus a1 a2"
      ) @ "ε"
    ) @ """let a2 = getA2
  plus a1 a2"""
  ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
  tBinding = Binding(
    ty = Auto() @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
    usage = Collapse(
      cTm = Return(v = Auto(), usage = Auto()) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b"""
    )
  ) @ "a",
  eff = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    tBinding = Binding(
      ty = Auto() @ """let b = getB
plus a b""",
      usage = Collapse(
        cTm = Return(v = Auto(), usage = Auto()) @ """let b = getB
plus a b"""
      )
    ) @ "b",
    eff = Auto(),
    body = Let(
      t = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
        t = Let(
          t = Return(v = Var(idx = 2) @ "a", usage = Auto()) @ "a",
          tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
          eff = Auto(),
          body = Redex(
            t = Def(qn = qn"__unresolved__.plus") @ "plus",
            elims = List(ETerm(v = Var(idx = 0)))
          ) @ "plus a"
        ),
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ "plus a b"
    )
  ) @ """let b = getB
plus a b"""
) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b"""