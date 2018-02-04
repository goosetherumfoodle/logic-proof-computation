(package provedit! [wff proof sequent tactic provedit! &l &r vl vr1 vr2 ~r ~l =>r =>l
                    <=>l <=>r swap thin lem lemma exp alll allr existsl existsr inter
                    =r =l term freesymbol exists all functor back proved undo
                    v & ~ => <=> falsum hyp *steps*]

(synonyms proof (list (step * string))
          sequent ((list wff) * wff)
          tactic (step --> step))

(datatype globals

  ________________________________
  (value *steps*) : (list symbol);)

(set *steps* [&l &r vl vr1 vr2 ~r ~l =>r =>l <=>l <=>r
              thin exp allr existsl lem =r =l back hyp])

(datatype step

 if (element? F (value *steps*))
 ____________________
 F : (step --> step);

 _____________________________
 lemma : (wff --> (step --> step));

 __________________________________
 thin : (number --> step --> step);

 if (element? F [alll existsr])
 ______________________________
 F : (term --> (step --> step));

 ______________________________________________
 swap : (number --> number --> step --> step);

 _________________________________________________
 introduce : (sequent --> (list sequent) --> step);

 Step : step;
 _____________________
 Step : (list sequent);)

(datatype freesymbol

if (not (element? P [& ~ v => <=> exists all = falsum]))
P : symbol;
___________
P : freesymbol;

S : symbol;
________________________
(gensym S) : freesymbol;

_____________________________________________
(freesymbol? S) : verified >> S : freesymbol;)

(datatype term

  F : freesymbol; X : (list term);
  =============================
  [F | X] : term;

  F : number;
  ___________
  F : term;

  F : string;
  ___________
  F : term;

  F : freesymbol;
  ___________
  F : term;

  F : boolean;
  ____________
  F : term;)

(datatype wff

X : term; Y : term;
===================
[X = Y] : wff;

P : wff;
============
[~ P] : wff;

if (element? C [v => <=> &])
P : wff; Q : wff;
=================
[P C Q] : wff;

if (element? Q [all exists])
X : freesymbol; P : wff;
========================
[Q X P] : wff;

P : freesymbol;
___________
P : wff;

___________
falsum : wff;

F : freesymbol; X : (list term);
===============================
[F | X] : wff;)

(define provedit!
  {--> boolean}
  -> (pass-loop (introduce (collect) []) []))

(define introduce
  {sequent --> (list sequent) --> (list sequent)}
   Sequent Sequents -> [Sequent | Sequents])

(define collect
   {--> sequent}
    -> (let NL (nl)
            Assumptions (input-assumptions 1)
            Prompt (output "~%>> ")
            Conclusion (input+ wff)
            Sequents (@p Assumptions Conclusion)
            Sequents))

(define input-assumptions
   {number --> (list wff)}
    N -> (let Prompt (output "~A. " N)
              (trap-error [(input+ wff) | (input-assumptions (+ N 1))] (/. E []))))

(define pass-loop
   {step --> proof --> boolean}
   Sequents Proof -> (do (print proved)
                         (store-proof? (reverse Proof))
                         true)    where (empty? Sequents)
   Sequents Proof -> (let Show (output (format-sequent Sequents (length Proof)))
                          Tactic (tactic)
                          (if (= Tactic undo)
                              (roll-back (do (output "how many steps do you want to undo? ")
                                             (trap-error (input+ number) (/. E 0)))
                                         Sequents
                                         Proof)
                              (pass-loop (Tactic Sequents)
                                     [(@p Sequents (it)) | Proof]))))

(define undo
  {A --> A}
   X -> X)

(define roll-back
 {number --> step --> proof --> boolean}
  0 Sequents Proof -> (pass-loop Sequents Proof)
  N _ [(@p Sequents _) | Proof] -> (roll-back (- N 1) Sequents Proof))

(define store-proof?
  {proof --> symbol}
  Proof -> (if (y-or-n? "~%save to file?")
               (trap-error (do (output "enter file name> ")
                               (write-to-file (input+ string) (format-proof Proof 1))
                               ok)
                           (/. E skip))
               skip))

(define format-proof
  {proof --> number --> string}
   [] _ -> "c#13;proved"
   [(@p Sequents Tactic) | Proof] N -> (@s (format-sequent Sequents N)
                                           (make-string "~%> ~A~%" Tactic)
                                           (format-proof Proof (+ N 1))))

(define tactic
  {--> tactic}
  -> (let Prompt (output "~%> " )
          (trap-error (input+ tactic)
                      (/. E (if (y-or-n? "Command not recognised; do you wish to abort the proof?")
                                (exit-provedit)
                                (tactic))))))

(define exit-provedit
  {--> A}
  -> (simple-error " "))

(define format-sequent
   {(list sequent) --> number --> string}
     [(@p Assumptions Conclusion) | Sequents] N
         -> (let Line (make-string "=========================~%Step ~A [~A]~%~%"
                             N
                             (length [(@p Assumptions Conclusion) | Sequents]))
               C (make-string "?- ~S~%~%" Conclusion)
               A (enumerate 1 Assumptions)
               (@s Line C A)))

(define enumerate
   {number --> (list A) --> string}
     _ [] -> " "
     N [X | Y] -> (cn (make-string "~A. ~S~%" N X)
                      (enumerate (+ N 1) Y)))

(define hyp
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents] -> Sequents
                               where (element? P Assumptions)
 Sequents -> Sequents)

(define &r
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [P & Q]) | Sequents]
     -> [(@p Assumptions P) (@p Assumptions Q)
           | Sequents]
  Sequents -> Sequents)

(define &l
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents]
   -> [(@p (split-& Assumptions) P) | Sequents]
  Sequents -> Sequents)

(define split-&
  {(list wff) --> (list wff)}
  []  -> []
  [[P & Q] | R] -> [P Q | R]
  [P | R] -> [P | (split-& R)])

(define vr1
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [P v Q]) | Sequents]
     -> [(@p Assumptions P) | Sequents]
  Sequents -> Sequents)

(define vr2
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [P v Q]) | Sequents]
     -> [(@p Assumptions Q) | Sequents]
  Sequents -> Sequents)

(define vl
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents]
     -> (let A*B (split-v Assumptions [])
               (if (= A*B (@p [] []))
                    [(@p Assumptions P) | Sequents]
                    [(@p (fst A*B) P)
                     (@p (snd A*B) P) | Sequents]))
  Sequents -> Sequents)

(define split-v
  {(list wff) --> (list wff)
            --> ((list wff) * (list wff))}
  [] _ -> (@p [] [])
  [[P v Q] | R] X -> (let RevX (reverse X)
                                  (@p (append RevX [P | R])
                                          (append RevX [Q | R])))
  [P | R] X -> (split-v R [P | X]))

(define =>r
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [P => Q]) | Sequents]
     -> [(@p [P | Assumptions] Q) | Sequents]
  Sequents -> Sequents)

(define =>l
  {(list sequent) --> (list sequent)}
  [(@p Assumptions Q) | Sequents]
     -> (let P (find-implication Assumptions Q)
            [(@p Assumptions P) | Sequents]))

(define find-implication
    {(list wff) --> wff --> wff}
    [] Q -> Q
   [[P => Q] | R] Q -> P
   [_ | R] Q -> (find-implication R Q))

(define ~r
    {(list sequent) --> (list sequent)}
    [(@p Assumptions [~ P]) | Sequents]
     -> [(@p Assumptions [P => falsum])
                     | Sequents]
  Sequents -> Sequents)

(define ~l
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents] -> [(@p (elim-~ Assumptions) P) | Sequents]
   Sequents -> Sequents)

(define elim-~
  {(list wff) --> (list wff)}
  [] -> []
  [[~ P] | R] -> [[P => falsum] | R]
  [P | R] -> [P | (elim-~ R)])

(define <=>r
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [P <=> Q]) | Sequents] -> [(@p Assumptions [[P => Q] & [Q => P]]) | Sequents]
  Sequents -> Sequents)

(define <=>l
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents] -> [(@p (elim-<=> Assumptions) P) | Sequents]
  Sequents -> Sequents)

(define elim-<=>
  {(list wff) --> (list wff)}
    [] -> []
    [[P <=> Q] | R] -> [[[P => Q] & [Q => P]] | R]
    [P | R] -> [P | (elim-<=> R)])

(define thin
   {number --> (list sequent) --> (list sequent)}
   N [(@p Assumptions P) | Sequents]
   -> [(@p (remove-nth N Assumptions) P) | Sequents])

(define remove-nth
   {number --> (list A) --> (list A)}
   1 [_ | Y] -> Y
   N [X | Y] -> [X | (remove-nth (- N 1) Y)])

(define swap
   {number --> number
       --> (list sequent) --> (list sequent)}
   M N [(@p Assumptions P) | Sequents]
   -> [(@p (trap-error (exchange M N Assumptions) (/. E Assumptions)) P) | Sequents])

(define exchange
   {number --> number --> (list A) --> (list A)}
    1 N [X | Y] -> [(nth N [X | Y]) | (insert X (- N 1) Y)]
    N 1 [X | Y] -> [(nth N [X | Y]) | (insert X (- N 1) Y)]
    M N [X | Y] -> [X | (exchange (- M 1) (- N 1) Y)]
    _ _ _ -> (error "cannot swap these items~%"))

(define insert
  {A --> number --> (list A) --> (list A)}
   X 1 [_ | Y] -> [X | Y]
   X N [Y | Z] -> [Y | (insert X (- N 1) Z)]
   _ _ _ -> (error "cannot swap these items~%"))

(define lemma
   {wff --> (list sequent) --> (list sequent)}
    P [(@p Assumptions Q) | Sequents]
    -> [(@p Assumptions P) (@p [P | Assumptions] Q) | Sequents])

(define lem
  {(list sequent) --> (list sequent)}
  [(@p _ [P v [~ P]]) | Sequents] -> Sequents
  Sequents -> Sequents)

(define exp
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents]
  -> [(@p Assumptions falsum) | Sequents]
  Sequents -> Sequents)

(define allr
  {(list sequent) --> (list sequent)}
  [(@p Assumptions [all X P]) | Sequents]
     -> [(@p Assumptions (replace (gensym term) X P)) | Sequents]
  Sequents -> Sequents)

(define replace
  {term --> term --> wff --> wff}
  Tm _ [all V P] -> [all V P]    where (== Tm V)
  Tm _ [exists V P] -> [exists V P]  where (== Tm V)
  Tm V [all X Y] -> [all X (replace Tm V Y)]
  Tm V [exists X Y] -> [exists X (replace Tm V Y)]
  Tm V [P v Q] -> [(replace Tm V P) v (replace Tm V Q)]
  Tm V [P & Q] -> [(replace Tm V P) & (replace Tm V Q)]
  Tm V [P => Q] -> [(replace Tm V P) => (replace Tm V Q)]
  Tm V [P <=> Q] -> [(replace Tm V P) <=> (replace Tm V Q)]
  Tm V [~ P] -> [~ (replace Tm V P)]
  Tm V [X = Y] -> [(replace* Tm V X) = (replace* Tm V Y)]
  Tm V [F | Terms] ->  [F | (map (/. Term (replace* Tm V Term)) Terms)]	 where (freesymbol? F)
  _ _ P -> P)

(define freesymbol?
  {A --> boolean}
   F -> (and (not (== F &)) (not (== F ~)) (not (== F v)) (not (== F =>))
             (not (== F <=>)) (not (== F exists)) (not (== F all)) (not (== F falsum))
             (symbol? F)))

(define replace*
  {term --> term --> term --> term}
  Tm V V -> Tm
  Tm V [Func | Tms] -> [Func | (map (/. Term (replace* Tm V Term)) Tms)]
  _ _ Term -> Term)

(define alll
  {term --> (list sequent) --> (list sequent)}
  Tm [(@p Assumptions P) | Sequents]
     -> [(@p (al-h Tm Assumptions) P) | Sequents]
  _ Sequents -> Sequents)

(define al-h
  {term --> (list wff) --> (list wff)}
  _ [] -> []
  Tm [[all X P] | Assumptions] -> [(replace Tm X P) [all X P] | Assumptions]
  Tm [Assumption | Assumptions] -> [Assumption | (al-h Tm Assumptions)])

(define existsr
  {term --> (list sequent) --> (list sequent)}
  Tm [(@p Assumptions [exists X P]) | Sequents]
     -> [(@p Assumptions (replace Tm X P)) | Sequents]
  _ Sequents -> Sequents)

(define existsl
  {(list sequent) --> (list sequent)}
  [(@p Assumptions P) | Sequents] -> [(@p (el-h Assumptions) P) | Sequents]
  Sequents -> Sequents)

(define el-h
  {(list wff) --> (list wff)}
  [] -> []
  [[exists X P] | Assumptions] -> [(replace (gensym term) X P) | Assumptions]
  [Assumption | Assumptions] -> [Assumption | (el-h Assumptions)])

(define =r
  {(list sequent) --> (list sequent)}
   [(@p _ [X = X]) | Sequents] -> Sequents
   Sequents -> Sequents)

(define =l
  {(list sequent) --> (list sequent)}
   [(@p Assumptions P) | Sequents] -> [(@p Assumptions (=l-h Assumptions P)) | Sequents]
   Sequents -> Sequents)

(define =l-h
  {(list wff) --> wff --> wff}
   [] P -> P
   [[X = Y] | _] P -> (replace Y X P)
   [_ | Assumptions] P -> (=l-h Assumptions P))   )
