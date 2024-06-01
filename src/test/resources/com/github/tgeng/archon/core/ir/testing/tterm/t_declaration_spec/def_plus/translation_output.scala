List(
  PreDefinition(
    qn = qn"test.plus",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
      ) @ "_",
      bodyTy = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
        ) @ "_",
        bodyTy = F(
          vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
          usage = Collapse(cTm = Return(v = Auto() @ "ε", usage = Auto()) @ "ε") @ "ε"
        ) @ "<> Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "Nat -> <> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> Nat -> <> Nat",
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
              t = Return(v = Var(idx = 0) @ "n", usage = Auto()) @ "n",
              tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
              eff = Auto(),
              body = Redex(
                t = Let(
                  t = Return(v = Var(idx = 2) @ "m", usage = Auto()) @ "m",
                  tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
                  eff = Auto(),
                  body = Redex(
                    t = Def(qn = qn"__unresolved__.plus") @ "plus",
                    elims = List(ETerm(v = Var(idx = 0) @ "ε"))
                  ) @ "plus m"
                ) @ "ε",
                elims = List(ETerm(v = Var(idx = 0)))
              ) @ "plus m n"
            ) @ "ε",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.Succ") @ "Succ",
              elims = List(ETerm(v = Var(idx = 0)))
            ) @ "Succ (plus m n"
          ) @ "ε"
        )
      )
    )
  )
)