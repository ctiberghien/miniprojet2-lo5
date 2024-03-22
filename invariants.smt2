; synthèse d'invariant de programme
; on déclare le symbole non interprété de relation Invar
(declare-fun Invar (Int Int Int) Bool)
; la relation Invar est un invariant de boucle
(assert (forall ( (x1 Int) (x2 Int) (x3 Int)) (=> (and (Invar x1 x2 x3) (> x3 x2)) (Invar (+ x1 x2) (+ x2 -4) (+ x3 x1)))))
; la relation Invar est vraie initialement
(assert (Invar 1 -2 4))
; l'assertion finale est vérifiée
(assert (forall ( (x1 Int) (x2 Int) (x3 Int)) (=> (and (Invar x1 x2 x3) (not(> x3 x2))) (= x3 -20))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit)