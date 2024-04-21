List(
  PreDefinition(
    qn = qn"test.foo",
    paramTys = List(),
    ty = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
        ) @ "_",
        bodyTy = Let(
          t = F(
            vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
            usage = Auto() @ "ε"
          ) @ "<> Nat",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "Nat -> <> Nat",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
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