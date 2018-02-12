(tc +)
(load "provedit!.shen")
(load "afst.shen")
(provedit!)

\* 6.2.2 [[[p v q] => [p v r]] => [p v [q => r]]] *\
\* 10.1.1 [[all x [F x]] <=> [~ [exists x [~ [F x]]]]] *\
\* 10.1.2 [all x [[~ [likes x beer]] => [~ [likes x guinness]]]],
          [all x [[likes x peanuts] => [likes x guinness]]],
        >>[all x [[likes x peanuts] => [likes x beer]]] *\
\* 10.1.3 [all x [all y [[ancestor x y] <=> [[parent x y] v [exists z [[anscestor z y] & [parent x z]]]]]]]
 , [parent tom sally]
 , [parent sally trisha]
 >>[anscestor tom trisha] *\

\* 10.1.3 [all x [all y [[A x y] <=> [[P x y] v [exists z [[A z y] & [P x z]]]]]]]
 , [P tom sally]
 , [P sally trisha]
 >>[A tom trisha] *\


\* 10.1.4 [exists z [[tall z] & [heavy z]]] >> [[exists x [tall x]] & [exists y [tall y]]] *\

\* 10.1.7 [all x [[M x] => [~ [I x]]]]
  ,[all x [[G x] => [I x]]]
 >>[all x [[M x] => [~ [G x]]]] *\

\* 10.1.8 [all x [[[M x] v [N x]] => [F x]]]
        , [all x [~ [F x]]]
        >>[all x [~ [N x]]] *\

\* 10.1.9 [all x [[L x] => [~ [H x]]]]
        , [exists x [[L x] & [W x]]]
        >>[exists x [[L x] & [~ [H x]]]] *\

\* 10.1.10 [all x [[[N x] v [M x]] => [F x]]]
         , [exists x [~ [F x]]]
         >>[exists x [~ [N x]]] *\

\* 10.1.11 [all x [all y [all z [F x y z]]]]
         >>[all z [all y [all x [F x y z]]]] *\

\* 10.1.12 [all x [exists y [all z [F x y z]]]]
         >>[all x [all z [exists y [F x y z]]]] *\

\* 10.1.13 [exists x [exists y [all z [F x y z]]]]
         >>[all z [exists y [exists x [F x y z]]]] *\
