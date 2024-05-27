List(
  PreDefinition(
    qn = qn"test.foo",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Return(v = Auto() @ "ε", usage = Auto()) @ "ε") @ "ε"
      ) @ "<> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> <> Nat",
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
              body = Redex(
                t = Def(qn = qn"__unresolved__.Suc") @ "Suc",
                elims = List(ETerm(v = Var(idx = 0) @ "ε"))
              ) @ "Suc Zero"
            ) @ "ε",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Redex(
              t = Let(
                t = Return(v = Var(idx = 1) @ "n", usage = Auto()) @ "n",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Redex(
                  t = Def(qn = qn"__unresolved__.plus") @ "plus",
                  elims = List(ETerm(v = Var(idx = 0)))
                ) @ "plus n"
              ) @ "ε",
              elims = List(ETerm(v = Var(idx = 0)))
            ) @ "plus n (Suc Zero"
          ) @ "ε"
        )
      )
    )
  )
)