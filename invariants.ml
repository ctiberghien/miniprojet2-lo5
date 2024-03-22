open Printf

(* Définitions de terme, test et programme *)

type term =
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test =
 | Equals of term * term
 | GreaterThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = GreaterThan (Const 0, Const 0)

type program = {nvars : int;
                inits : int list;
                mods : term list;
                loopcond : test;
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string`
   et `str_of_test : test -> string` qui convertissent des termes
   et des tests en chaînes de caractères du format SMT-LIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)". *)

let rec str_of_term t =
  match t with
  | Const c -> string_of_int c
  | Var v -> x v
  | Add (t1,t2) -> "(+ "^str_of_term t1 ^" "^ str_of_term t2^")"
  | Mult (t1,t2) -> "(*"^str_of_term t1 ^" "^ str_of_term t2^")"

let rec str_of_test t =
  match t with
  | Equals (t1,t2) -> "(= "^str_of_term t1 ^" "^ str_of_term t2^")"
  | GreaterThan (t1,t2) -> "(> "^str_of_term t1 ^" "^ str_of_term t2^")"

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne
   de caractères qui exprime que le tuple (t1, ..., tk) est dans
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne
   "(Invar x1 10)". *)

let str_condition l =
  let rec aux l =
    match l with
    | [] -> ""
    (*pour chaque terme de la liste on ajoute son terme convertit en string*)
    | x::reste -> " "^str_of_term x^aux reste
  (*on commence par écrire (Invar) et on remplit à l'intérieur *)
  in "(Invar"^aux l^")" 

(* Question 3. Écrire une fonction
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMT-LIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "> x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (> x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^ ")"

 let str_assert_forall n s =
  (* i est un compteur de l'écriture de chaque terme*)
  let rec aux i =
    (* si on a écrit n-1 termes on peut écrire le dernier terme et terminer*)
    if i = n then " ("^(x i)^" Int)" 
    (* sinon on écrit le i-ème terme et on continue avec i+1*)
    else " ("^(x i)^" Int)"^aux (i+1)
  (*on commence par écrire (forall()) et on remplit à l'intérieur de la première parenthès puis on ajoute (s)*)
  in str_assert ("(forall ("^aux 1^") ("^s^"))")


(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

(* vars permet de d'afficher (Invar x1 ... xi) *)
let vars nvars =
  let rec aux i =
    if i=1 then (x i)^aux (i+1)
    else if i=nvars then " "^(x i)
    else " "^(x i)^aux (i+1)
  in "(Invar "^(aux 1)^")"

let smtlib_of_wa p =
  let declare_invariant =
    "; synthèse d'invariant de programme\n"
    ^ "; on déclare le symbole non interprété de relation Invar\n"
    (* on commence par écrire (declare-fun Invar (Int) Bool) avec p.nvars-1 fois Int*)
    ^ "(declare-fun Invar (Int"^ string_repeat " Int" (p.nvars-1) ^  ") Bool)" in
  let loop_condition =
    "; la relation Invar est un invariant de boucle\n"
    (* on appelle str_assert_forall on aura donc la partie assert et forall composé de ( (x1 Int) ... (xi Int)) 
      et de (=> (and -vars- -str_of_test-) (-str_condition-))*)
    ^ str_assert_forall p.nvars ("=> (and "^ (vars p.nvars) ^ " " ^ (str_of_test p.loopcond) ^ ") " ^ str_condition p.mods) in

  let initial_condition =
    "; la relation Invar est vraie initialement\n"
    ^ str_assert (str_condition (List.map (function i -> Const i) p.inits)) in
  let assertion_condition =
    "; l'assertion finale est vérifiée\n"
    (* ici on fait la même chose que dans loop_condition mais on rajoute un not devant str_of_test*)
     ^ str_assert_forall p.nvars ("=> (and " ^ (vars p.nvars) ^ " (not" ^ (str_of_test p.loopcond) ^ ")) " ^ (str_of_test p.assertion)) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant;
                      loop_condition;
                      initial_condition;
                      assertion_condition;
                      call_solver]

let p1 = {nvars = 2;
          inits = [4 ; 0];
          mods = [Add ((Var 1), (Const (-1)));Add ((Var 2), (Var 1))];
          loopcond = GreaterThan ((Var 1), (Const 0));
          assertion = Equals ((Var 2),(Const 10))}

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMT-LIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. *)

let () = Printf.printf "%s" (smtlib_of_wa p1)

(* Ajoutez dans la variable p2 ci-dessous au moins un autre programme
   test avec **trois** variables et vérifiez qu'il donne un fichier
   SMT-LIB la forme attendue. *)

let p2 = {nvars = 3;
          inits = [1 ; -2 ; 4];
          mods = [Add ((Var 1), (Var 2)); Add((Var 2), (Const (-4))); Add ((Var 3), (Var 1))];
          loopcond = GreaterThan ((Var 3), (Var 2));
          assertion = Equals ((Var 3),(Const (-20)))}


let () = Printf.printf "%s" (smtlib_of_wa p2)
