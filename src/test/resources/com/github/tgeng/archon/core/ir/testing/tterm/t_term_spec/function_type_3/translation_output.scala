FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A",
    usage = Collapse(cTm = Def(qn = qn"__unresolved__.uA") @ "uA") @ "uA"
  ) @ "a",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "B",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uB") @ "uB") @ "uB"
    ) @ "b",
    bodyTy = F(
      vTy = Collapse(
        cTm = Redex(
          t = Def(qn = qn"__unresolved__.C") @ "C",
          elims = List(ETerm(v = Var(idx = 1) @ "a"), ETerm(v = Var(idx = 0) @ "b"))
        ) @ "C a b"
      ) @ "C a b",
      effects = Collapse(cTm = Def(qn = qn"__unresolved__.effC") @ "effC") @ "effC",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uC") @ "uC") @ "uC"
    ) @ "<effC> [uC] C a b",
    effects = Collapse(cTm = Def(qn = qn"__unresolved__.effB") @ "effB") @ "effB",
    escapeStatus = EsUnknown
  ) @ "b: [uB] B -> <effC> [uC] C a b",
  effects = Collapse(cTm = Def(qn = qn"__unresolved__.effA") @ "effA") @ "effA",
  escapeStatus = EsUnknown
) @ "a: [uA] A -> <effB> b: [uB] B -> <effC> [uC] C a b"