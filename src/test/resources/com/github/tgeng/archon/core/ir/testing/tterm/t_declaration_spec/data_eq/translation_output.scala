List(
  PreData(
    qn = qn"test.Eq",
    tParamTys = List(
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Level") @ "Level",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ) @ "l",
        INVARIANT
      ),
      (
        Binding(
          ty = Let(
            t = Def(qn = qn"__unresolved__.l") @ "l",
            tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
            eff = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.Type") @ "Type",
              elims = List(ETerm(v = Var(idx = 0) @ "l"))
            ) @ "Type l"
          ) @ "ε",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "A",
        INVARIANT
      ),
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.A") @ "A",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "x",
        INVARIANT
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny")) @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(
          cTm = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l") @ "l"))
          ) @ "Type l"
        ) @ "Type l",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1") @ "ε") @ "ε"
      ) @ "Type l",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "A -> Type l",
    constructors = List(
      PreConstructor(
        name = n"Refl",
        ty = F(
          vTy = Collapse(
            cTm = Redex(
              t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
              elims = List(
                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l") @ "l"),
                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A"),
                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x") @ "x"),
                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x") @ "x")
              )
            ) @ "Eq l A x x"
          ) @ "Eq l A x x",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
        ) @ "Eq l A x x"
      )
    )
  )
)