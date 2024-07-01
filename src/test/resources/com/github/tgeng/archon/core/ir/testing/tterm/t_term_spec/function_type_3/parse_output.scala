TFunctionType(
  arg = TBinding(name = "a", ty = TId(id = "A") @ "A", usage = TId(id = "uA") @ "uA"),
  bodyType = TFunctionType(
    arg = TBinding(name = "b", ty = TId(id = "B") @ "B", usage = TId(id = "uB") @ "uB"),
    bodyType = TF(
      ty = TRedex(
        c = TId(id = "C") @ "C",
        elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
      ) @ "C a b",
      effects = TId(id = "effC") @ "effC",
      usage = TId(id = "uC") @ "uC"
    ) @ "<effC> [uC] C a b",
    effects = TId(id = "effB") @ "effB"
  ) @ "b: [uB] B -> <effC> [uC] C a b",
  effects = TId(id = "effA") @ "effA"
) @ "a: [uA] A -> <effB> b: [uB] B -> <effC> [uC] C a b"