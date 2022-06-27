Let(
  Let(
    Def(root.Nat.Z), Application(Def(root.Nat.S), Var(0))
  ), Let(
    Application(Def(root.Nat.S), Var(0))
    , Let(
      Application(Def(root.Nat.S), Var(0))
      , Let(Def(.archon.builtin.effects.total)
      , Let(
        Def(root.Nat)
        , Handler(
          (root.dice, List(Var(2)))
          , Var(1)
          , Var(0)
          , Return(Var(0))
          , Map(
            roll -> Let(
              Let(
                Let(
                  Application(Def(root.Fin.FZ), Var(4)),
                  Application(Force(Var(1)), Var(0))
                ),
                Let(
                  Let(
                    Let(
                      Application(Def(root.Fin.FZ), Var(6)),
                      Application(
                        Application(Def(root.Fin.FS), Var(6)),
                        Var(0)
                      )
                    ),
                    Application(Force(Var(2)), Var(0))
                  ), Application(
                    Application(Def(root.plus), Var(1)), Var(0)
                  )
                )
              ), Let(
                Let(
                  Let(
                    Let(
                      Let(
                        Def(root.Nat.Z),
                        Application(
                          Def(root.Fin.FZ),
                          Var(0)
                        )
                      ), Application(
                        Application(Def(root.Fin.FS), Var(7)), Var(0)
                      )
                    )
                    , Application(
                      Application(Def(root.Fin.FS), Var(6))
                      , Var(0)
                    )
                  ), Application(Force(Var(2)), Var(0))
                ), Application(
                  Application(Def(root.plus), Var(1))
                  , Var(0)
                )
              )
            )
          ), Let(
            Application(Def(root.dice.roll), Var(2))
            , Application(
              Application(Def(root.finToNat), Var(3))
              , Var(0)
            )
          )
        )
      )
    )
  )
)
)