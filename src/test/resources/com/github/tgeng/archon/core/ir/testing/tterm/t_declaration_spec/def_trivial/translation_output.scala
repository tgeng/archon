List(
  PreDefinition(
    qn = qn"test.foo",
    paramTys = List(),
    ty = Let(
      t = Def(qn = qn"archon.builtin.effects.total") @ "ε",
      ty = Auto() @ "ε",
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = FunctionType(
              binding = Binding(ty = Var(idx = 0) @ "ε", usage = Var(idx = 0)) @ "_",
              bodyTy = Let(
                t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = Def(qn = qn"archon.builtin.effects.total"),
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Let(
                    t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Auto()) @ "<> Nat",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                  ) @ "ε"
                ) @ "ε"
              ) @ "ε",
              effects = Var(idx = 0)
            ) @ "Nat -> <> Nat",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Return(v = Var(idx = 0), usage = Auto())
          ) @ "ε"
        ) @ "ε"
      ) @ "ε"
    ) @ "ε",
    clauses = List(
      PreClause(
        boundNames = List("n"),
        lhs = List(CPattern(pattern = PVar(idx = 0))),
        rhs = Some(
          value = Let(
            t = Let(
              t = Def(qn = qn"__unresolved__.Zero") @ "Zero",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = Redex(
                  t = Def(qn = qn"__unresolved__.Suc") @ "Suc",
                  elims = List(ETerm(v = Var(idx = 0)))
                ) @ "Suc Zero",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Redex(
                t = Let(
                  t = Redex(
                    t = Def(qn = qn"__unresolved__.plus") @ "plus",
                    elims = List(ETerm(v = Var(idx = 1) @ "n"))
                  ) @ "plus n",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε",
                elims = List(ETerm(v = Var(idx = 0)))
              ) @ "plus n (Suc Zero",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ) @ "ε"
          ) @ "ε"
        )
      )
    )
  )
)