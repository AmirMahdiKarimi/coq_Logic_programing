(* 
    AmirMahdi Karimi - 610302065
     Implementation of Lambda2 
*)

Import Nat.
Require Import List.
Import List.ListNotations.


Inductive Type2 : Type :=
| Tvar: nat -> Type2
| Tarrow: Type2 -> Type2 -> Type2
| Tforall: nat -> Type2 -> Type2.

Definition sample_Tvar := Tvar 1.
Definition sample_Tarrow := Tarrow (Tvar 1) (Tvar 2).
Definition sample_Tforall := Tforall 1 (Tarrow (Tvar 1) (Tvar 2)).

Inductive Term: Type :=
| tvar: nat -> Term
| tapp: Term -> Term -> Term 
| tTapp: Term -> Type2 -> Term 
| tabs: nat -> Term -> Term
| tTabs: nat -> Term -> Term.

Definition sample_tvar := tvar 1.
Definition sample_tabs := tabs 1 (tvar 2).
Definition sample_tTabs := tTabs 1 (tvar 2).
Definition sample_tapp := tapp (sample_tabs) (tvar 2).
Definition sample_tTapp := tTapp (sample_tTabs) (Tvar 2).

Fixpoint remove_eqb (n: nat) (l: list nat) : list nat :=
    match l with
    | nil => nil
    | x :: xs => if eqb x n then remove_eqb n xs else x :: remove_eqb n xs
    end.

Check remove_eqb 1 [1; 2; 3; 1; 4] = [2; 3; 4].
    
Fixpoint free_vars (t: Type2) : list nat :=
    match t with
    | Tvar v => [v]
    | Tarrow t1 t2 => (free_vars t1) ++ (free_vars t2)
    | Tforall v t1 => remove_eqb v (free_vars t1)
    end.

Check free_vars sample_Tvar = [1]. 
Check free_vars sample_Tarrow = [1; 2]. 
Check free_vars sample_Tforall = [2]. 

Fixpoint is_type_eqb (t1 t2: Type2) : bool :=
    match t1, t2 with
    | Tvar a, Tvar b => eqb a b
    | Tarrow a b, Tarrow a' b' => (is_type_eqb a a') && (is_type_eqb b b')
    | Tforall a b, Tforall a' b' => (eqb a a') && (is_type_eqb b b')
    | _, _ => false 
    end.

Check is_type_eqb sample_Tvar (Tvar 1) = true. 
Check is_type_eqb sample_Tarrow (Tarrow (Tvar 1) (Tvar 2)) = true.
Check is_type_eqb sample_Tarrow (Tarrow (Tvar 2) (Tvar 1)) = false.

Fixpoint is_term_eqb (t1 t2: Term) : bool :=
    match t1, t2 with
    | tvar a, tvar b => eqb a b 
    | tapp a b, tapp a' b' => (is_term_eqb a a') && (is_term_eqb b b')
    | tTapp a b, tTapp a' b' => (is_term_eqb a a') && (is_type_eqb b b')
    | tabs a b, tabs a' b' => (eqb a a') && (is_term_eqb b b')
    | tTabs a b, tTabs a' b' => (eqb a a') && (is_term_eqb b b')
    | _, _ => false 
    end.

Check is_term_eqb sample_tvar (tvar 1) = true.
Check is_term_eqb sample_tapp (tapp (tabs 1 (tvar 2)) (tvar 2)) = true.
Check is_term_eqb sample_tapp (tapp (tvar 2) (tabs 1 (tvar 2))) = false.

Inductive ContextType : Type := 
| type_context : nat -> ContextType
| term_context : nat -> Type2 -> ContextType.
Definition Context : Type := list ContextType.

Definition sample_context : Context := [term_context 1 (Tvar 2); type_context 1].

Fixpoint check_term (t : Term) (ctx : Context) : bool := 
    match ctx with
    | nil => false
    | d :: ctx' => match d with  
        | term_context idx ty => (is_term_eqb t (tvar idx)) || (check_term t ctx')
        | type_context _ => check_term t ctx'
        end
    end.

Check check_term (tvar 1) sample_context = true.
Check check_term (tvar 2) sample_context = false.

Fixpoint check_type (idx : nat) (ctx : Context) : bool :=
    match ctx with
    | nil => false
    | d :: ctx' => match d with
        | term_context _ _ => check_type idx ctx'
        | type_context index => (eqb index idx) || (check_type idx ctx')
        end
    end.

Check check_type 1 sample_context = true.
Check check_type 2 sample_context = false.
