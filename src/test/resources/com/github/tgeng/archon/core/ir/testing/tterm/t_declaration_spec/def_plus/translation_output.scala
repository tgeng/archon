List(
  PreDefinition(
    qn = qn"test.plus",
    paramTys = List(),
    ty = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
        ) @ "_",
        bodyTy = Let(
          t = FunctionType(
            binding = Binding(
              ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
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
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "Nat -> Nat -> <> Nat",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    clauses = List(
      PreClause(
        boundNames = List("n"),
        lhs = List(
          CPattern(pattern = PDataType(qn = qn"__unresolved__.Zero", args = List())),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(value = Return(v = Var(idx = 0) @ "n", usage = Auto()) @ "n")
      ),
      PreClause(
        boundNames = List("m", "n"),
        lhs = List(
          CPattern(pattern = PDataType(qn = qn"__unresolved__.Succ", args = List(PVar(idx = 1)))),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(
          value = Let(
            t = Let(
              t = Redex(
                t = Let(
                  t = Redex(
                    t = Def(qn = qn"__unresolved__.plus") @ "plus",
                    elims = List(ETerm(v = Var(idx = 2) @ "m"))
                  ) @ "plus m",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε",
                elims = List(ETerm(v = Var(idx = 0) @ "n"))
              ) @ "plus m n",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ) @ "ε",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Redex(
                t = Def(qn = qn"__unresolved__.Succ") @ "Succ",
                elims = List(ETerm(v = Var(idx = 0)))
              ) @ "Succ (plus m n",
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