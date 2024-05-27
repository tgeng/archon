FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
    usage = Collapse(cTm = Def(qn = qn"__unresolved__.uA") @ "uA") @ "ε"
  ) @ "a",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uB") @ "uB") @ "ε"
    ) @ "b",
    bodyTy = F(
      vTy = Collapse(
        cTm = Redex(
          t = Redex(
            t = Def(qn = qn"__unresolved__.C") @ "C",
            elims = List(
              ETerm(
                v = Collapse(cTm = Return(v = Var(idx = 5) @ "a", usage = Auto() @ "ε") @ "a") @ "ε"
              )
            )
          ) @ "C a",
          elims = List(
            ETerm(v = Collapse(cTm = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b") @ "ε")
          )
        ) @ "C a b"
      ) @ "ε",
      effects = Collapse(cTm = Def(qn = qn"__unresolved__.effC") @ "effC") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uC") @ "uC") @ "ε"
    ) @ "<effC> [uC] C a b",
    effects = Collapse(cTm = Def(qn = qn"__unresolved__.effB") @ "effB") @ "ε"
  ) @ "b: [uB] B -> <effC> [uC] C a b",
  effects = Collapse(cTm = Def(qn = qn"__unresolved__.effA") @ "effA") @ "ε"
) @ "a: [uA] A -> <effB> b: [uB] B -> <effC> [uC] C a b"