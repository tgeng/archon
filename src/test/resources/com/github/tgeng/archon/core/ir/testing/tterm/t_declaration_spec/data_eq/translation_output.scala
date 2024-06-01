List(
  PreData(
    qn = qn"test.Eq",
    tParamTys = List(
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Level") @ "Level",
          usage = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε"
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
              elims = List(ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "Type l"
          ) @ "ε",
          usage = Def(qn = qn"archon.builtin.type.Usage.any")
        ) @ "A",
        INVARIANT
      ),
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.A") @ "A",
          usage = Def(qn = qn"archon.builtin.type.Usage.any")
        ) @ "x",
        INVARIANT
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any")) @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(
          cTm = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l") @ "ε"))
          ) @ "Type l"
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε") @ "ε"
      ) @ "Type l",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "A -> Type l",
    constructors = List(
      PreConstructor(
        name = n"Refl",
        ty = F(
          vTy = Collapse(
            cTm = Redex(
              t = Redex(
                t = Redex(
                  t = Redex(
                    t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
                    elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l")))
                  ) @ "Eq l",
                  elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A")))
                ) @ "Eq l A",
                elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x") @ "ε"))
              ) @ "Eq l A x",
              elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x")))
            ) @ "Eq l A x x"
          ) @ "ε",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
        ) @ "Eq l A x x"
      )
    )
  )
)