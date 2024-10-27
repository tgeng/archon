List(
  PreDefinition(
    qn = qn"test.foo",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Auto() @ "ε"
      ) @ "<> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
      escapeStatus = EsLocal
    ) @ "Nat -> <> Nat",
    clauses = List(
      PreClause(
        boundNames = List("n"),
        lhs = List(CPattern(pattern = PVar(idx = 0))),
        rhs = Some(
          value = Let(
            t = Let(
              t = Def(qn = qn"__unresolved__.Zero") @ "Zero",
              tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
              eff = Auto(),
              body = Redex(
                t = Def(qn = qn"__unresolved__.Suc") @ "Suc",
                elims = List(ETerm(v = Var(idx = 0) @ "Zero"))
              ) @ "Suc Zero"
            ) @ "ε",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.plus") @ "plus",
              elims = List(ETerm(v = Var(idx = 0) @ "n"), ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "plus n (Suc Zero)"
          ) @ "ε"
        )
      )
    )
  )
)