Let(
  t = Let(
    t = Let(
      t = Let(
        t = Def(qn = qn"__unresolved__.getA1") @ "getA1",
        ty = Auto() @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Let(
            t = Def(qn = qn"__unresolved__.getA2") @ "getA2",
            ty = Auto() @ """let a2 = getA2
  plus a1 a2""",
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Redex(
                t = Let(
                  t = Redex(
                    t = Def(qn = qn"__unresolved__.plus") @ "plus",
                    elims = List(ETerm(v = Var(idx = 5) @ "a1"))
                  ) @ "plus a1",
                  ty = Auto() @ "ε",
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
                ) @ "ε",
                elims = List(ETerm(v = Var(idx = 0) @ "a2"))
              ) @ "plus a1 a2",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ) @ "ε"
          ) @ """let a2 = getA2
  plus a1 a2""",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    ty = Auto() @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Let(
        t = Def(qn = qn"__unresolved__.getB") @ "getB",
        ty = Auto() @ """let b = getB
plus a b""",
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Redex(
            t = Let(
              t = Redex(
                t = Def(qn = qn"__unresolved__.plus") @ "plus",
                elims = List(ETerm(v = Var(idx = 5) @ "a"))
              ) @ "plus a",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ),
            elims = List(ETerm(v = Var(idx = 0) @ "b"))
          ) @ "plus a b",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        )
      ) @ """let b = getB
plus a b""",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε"
  ) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Return(v = Var(idx = 0), usage = Auto())
) @ "ε"