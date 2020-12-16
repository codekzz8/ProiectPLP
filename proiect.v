Include Nat.
Require Import Omega.
Set Nested Proofs Allowed.

Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

Require Import List.
Local Open Scope list_scope.
Scheme Equality for list.
Import ListNotations.

Require Export BinNums.
Require Import BinPos BinNat.
Local Open Scope Z_scope.

Inductive ErrorInt :=
| err_int : ErrorInt
| num : Z -> ErrorInt.

Coercion num : Z >-> ErrorInt.

Inductive ErrorBool :=
| err_bool : ErrorBool
| bbool : bool -> ErrorBool.

Coercion bbool : bool >-> ErrorBool.

(* Tipuri de rezultate *)
Inductive Results :=
| err_undecl : Results
| err_assign : Results
| rint : ErrorInt -> Results
| rbool : ErrorBool -> Results
| default : Results.
Scheme Equality for Results.

(* Expresii aritmetice *)
Inductive AExp :=
| aint : ErrorInt -> AExp
| avar : string -> AExp
| arrayVal : string -> nat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| amax : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| apow : AExp -> AExp -> AExp
| adefault : AExp.

Coercion aint : ErrorInt >-> AExp.
Coercion avar : string >-> AExp.

(* Expresii booleene *)
Inductive BExp :=
| berr
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| beq : AExp -> AExp -> BExp
| blt : AExp -> AExp -> BExp
| ble : AExp -> AExp -> BExp
| bgt : AExp -> AExp -> BExp
| bge : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Coercion bvar : string >-> BExp.

Definition arr_list := list Z.

(* Tipuri de statementuri *)
Inductive Stmt :=
| assignment_int : string -> AExp -> Stmt
| assignment_array : string -> Z -> AExp -> arr_list -> Stmt
| assignment_bool : string -> BExp -> Stmt
| adecboolnull : string -> Stmt
| adecbool : string -> BExp -> Stmt
| adecintnull : string -> Stmt
| adecint : string -> AExp -> Stmt
| adecarray : string -> AExp -> arr_list -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| whilethisdothat : BExp -> Stmt -> Stmt
| forthisdothat : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| define_int : string -> AExp -> Stmt
| define_bool : string -> BExp -> Stmt
| switch : AExp -> list (AExp * Stmt) -> Stmt
| label : string -> Stmt -> Stmt
| goto : string -> Stmt.

(* Notatii pentru expresii aritmetice *)
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Notation "'min' '(' A ',' B ')'" := (amin A B) (at level 45).
Notation "'max' '(' A ',' B ')'" := (amax A B) (at level 45).
Notation "'pow' '(' A ',' B ')'" := (apow A B) (at level 45).
Notation "A '::'' i" := (arrayVal A i) (at level 44).
Notation "'Default'" := (adefault) (at level 60).

(* Verificari AExp *)
Check -2 +' 3.
Check -1 -' 5.
Check 2 *' -3.
Check 2 /' 0.
Check 5 %' 2.
Check min(1, 2).
Check max(3, 5).
Check pow(2, 10).

(* Notatii pentru expresii booleene *)
Notation "! A" := (bnot A) (at level 50).
Notation "A ==' B" := (beq A B) (at level 55).
Notation "A <' B" := (blt A B) (at level 55).
Notation "A <=' B" := (ble A B) (at level 55).
Notation "A >' B" := (bgt A B) (at level 55).
Notation "A >=' B" := (bge A B) (at level 55).
Notation "A '&&'' B" := (band A B) (at level 54).
Notation "A '||'' B" := (bor A B) (at level 54).

(* Verificari BExp *)
Check !btrue.
Check 1 ==' 1.
Check -1 <' 3.
Check 0 <=' 2.
Check 1 >' 0.
Check 2 >=' 2.
Check btrue &&' bfalse.
Check btrue ||' bfalse.

(* Notatii statementuri *)
Notation "'int*' A" := (adecintnull A) (at level 50).
Notation "'int' A =' B" := (adecint A B) (at level 50).
Notation "'boolean*' A" := (adecboolnull A) (at level 56).
Notation "'boolean' A =' B" := (adecbool A B) (at level 56).
Notation "'array' A '['' B '']' L" := (adecarray A B L) (at level 50).
Notation "X '#' i ::=a A" := (assignment_array X i A) (at level 50).
Notation "X ::=n A" := (assignment_int X A) (at level 50).
Notation "X ::=b A" := (assignment_bool X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 60).
Notation "'Iff' A 'Then' B" := (ifthen A B) (at level 70).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 70).
Notation "'While' '(' A ')' '(' B ')'" := (whilethisdothat A B) (at level 90).
Notation "'For' '(' A ; B ; C ')' '(' D ')'" := (forthisdothat A B C D) (at level 90).
Notation "A :' B" := (label A B) (at level 90).
Notation "'Switch' '(' A ')' B " := (switch A B) (at level 70).
Notation "'case_int' A" := (aint A) (at level 60).
Notation "'case_var' A" := (avar A) (at level 60).

(* Verificari Stmt *)
Check Switch(min("a","b"))
      [
        (case_var "a", "rez" ::=n 1;;
                       break)
                       ;
        (case_var "b", "rez" ::=n 2;;
                       break)
                       ;
        (Default,      "rez" ::=n 0;;
                       break)
      ].

Check Switch(min("a","b"))
      [
        (case_int 1, "rez" ::=n 1;;
                     "rez" ::=n ("rez" +' 1);;
                     break)
                     ;
        (case_int 2, "rez" ::=n 2;;
                     "rez" ::=n ("rez" %' 2);;
                     break)
      ].

Check boolean* "ok".
Check boolean "ok" =' bfalse.

Check int* "sum".
Check int "sum" =' 0.
Check array "a"['"MAX"'] [].
Check array "b"['10'] [].
Check "a"#0 ::=a 3.
Check "a"#0 ::=a "Andrei".
Check "a"::'3.
Check define_int "MAX" 1000.
Check define_bool "OK" btrue.
Check "sum" ::=n 51.
Check "sum" ::=n 0;;
      "sum" ::=n ("sum" +' 1).
Check Iff (1 <' 3)
      Then "x" ::=n 3.
Check If (1 <=' -2)
      Then "x" ::=b btrue
      Else "x" ::=b bfalse.
Check While (btrue)
      (
        "sum" ::=n ("sum" -' 1)
      ).
Check For ("i" ::=n 0; "i" <=' 10; "i" ::=n ("i" +' 1))
      (
        "sum" ::=n ("sum" /' "i")
      ).
Check break.
Check continue.
Check "label" :'
      "x" ::=n 2;; 
      Iff ("x" ==' 2) Then "x" ::=n 3.
Check goto "label".

Definition Env := string -> Results.

(* Verifica starea unei variabile *)
Definition CheckType (a : Results) (b : Results) : bool :=
match a with
| err_undecl => match b with
                | err_undecl => true
                | _ => false
                end
| err_assign => match b with
                | err_assign => true
                | _ => false
                end
| rint x => match b with
                | rint _y => true
                | _ => false
                end
| rbool x => match b with
                | rbool _y => true
                | _ => false
                end
| default => match b with
                | default => true
                | _ => false
                end
end.

(* lookup *)
Definition env : Env := fun n => err_undecl.

(* update *)
Definition update (env : Env) (x : string) (v : Results) : Env :=
  fun y => if (eqb y x)
            then
              if (andb (CheckType err_undecl (env y)) (negb(CheckType default v)))
              then err_undecl
              else
                if (andb (CheckType err_undecl (env y)) (CheckType default v))
                then default
                else
                  if (orb (CheckType default (env y)) (CheckType v (env y)))
                  then v
                  else err_assign
            else (env y).

Compute (env "x").
Compute (update (update env "x" (default)) "x" (rbool true) "x").

(*-----------------------------------------------------------*)
(*                       SEMANTICA                           *)
(*-----------------------------------------------------------*)

(* Definitii AExp *)
Definition plus_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err_int, _ => err_int
    | _, err_int => err_int
    | num v1, num v2 => num (v1 + v2)
    end.
Compute plus_err err_int 2.
Compute plus_err 1 2.

Definition minus_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err_int, _ => err_int
    | _, err_int => err_int
    | num v1, num v2 => num (v1 + v2)
    end.
Compute minus_err 3 err_int .
Compute minus_err 3 1.

Definition mul_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err_int, _ => err_int
    | _, err_int => err_int
    | num v1, num v2 => num (v1 * v2)
    end.
Compute mul_err 4 3.

Definition div_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err_int, _ => err_int
    | _, err_int => err_int
    | _, num 0 => err_int
    | num v1, num v2 => num (Z.div v1 v2)
    end.
Compute div_err 5 0.
Compute div_err 10 2.

Definition mod_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err_int, _ => err_int
    | _, err_int => err_int
    | _, num 0 => err_int
    | num v1, num v2 => num (Z.modulo v1 v2)
    end.
Compute mod_err 4 0.
Compute mod_err 35 2.

(* Definitii BExp *)
Definition eq_err (n1 n2 : ErrorInt) : ErrorBool :=
match n1, n2 with
| err_int, _ => err_bool
| _, err_int => err_bool
| num v1, num v2 => bbool (Z.eqb v1 v2)
end.
Check eq_err 2 2.

Definition lt_err (n1 n2 : ErrorInt) : ErrorBool :=
match n1, n2 with
| err_int, _ => err_bool
| _, err_int => err_bool
| num v1, num v2 => bbool (Z.ltb v1 v2)
end.
Check lt_err 5 2.

Definition le_err (n1 n2 : ErrorInt) : ErrorBool :=
match n1, n2 with
| err_int, _ => err_bool
| _, err_int => err_bool
| num v1, num v2 => bbool (Z.leb v1 v2)
end.
Check le_err 1 1.

Definition gt_err (n1 n2 : ErrorInt) : ErrorBool :=
match n1, n2 with
| err_int, _ => err_bool
| _, err_int => err_bool
| num v1, num v2 => bbool (Z.gtb v1 v2)
end.
Check gt_err 5 2.

Definition ge_err (n1 n2 : ErrorInt) : ErrorBool :=
match n1, n2 with
| err_int, _ => err_bool
| _, err_int => err_bool
| num v1, num v2 => bbool (Z.geb v1 v2)
end.
Check gt_err 6 6.

Definition not_err (n : ErrorBool) : ErrorBool :=
match n with
| err_bool => err_bool
| bbool v => bbool (negb v)
end.
Check not_err true.

Definition and_err (n1 n2 : ErrorBool) : ErrorBool :=
match n1, n2 with
| err_bool, _ => err_bool
| _, err_bool => err_bool
| bbool v1, bbool v2 => bbool (andb v1 v2)
end.
Check and_err true false.

Definition or_err (n1 n2 : ErrorBool) : ErrorBool :=
match n1, n2 with
| err_bool, _ => err_bool
| _, err_bool => err_bool
| bbool v1, bbool v2 => bbool (orb v1 v2)
end.
Check or_err true false.

Reserved Notation "A =[ S ]=> N" (at level 65).
Inductive aeval : AExp -> Env -> ErrorInt -> Prop :=
| const : forall n sigma, aint n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                            | rint x => x
                                            | _ => err_int
                                            end
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = plus_err i1 i2 ->
    a1 +' a2 =[ sigma ]=> n
| sub' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = minus_err i1 i2 ->
    a1 -' a2 =[ sigma ]=> n
| mul' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mul_err i1 i2 ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = div_err i1 i2 ->
    a1 /' a2 =[ sigma ]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mod_err i1 i2 ->
    a1 %' a2 =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| e_err : forall sigma, berr ={ sigma }=> err_bool
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = eq_err i1 i2 ->
    a1 ==' a2 ={ sigma }=> b
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = lt_err i1 i2 ->
    (a1 <' a2) ={ sigma }=> b
| e_lessequalthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = le_err i1 i2 ->
    (a1 <=' a2) ={ sigma }=> b
| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = gt_err i1 i2 ->
    (a1 >' a2) ={ sigma }=> b
| e_greaterequalthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = ge_err i1 i2 ->
    (a1 >=' a2) ={ sigma }=> b
| e_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_err i1) ->
    (! a1) ={ sigma }=> b
| e_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_err i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b
| e_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_err i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').

Reserved Notation "S -{ sigma }-> Sigma'" (at level 60).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_int_decl_null : forall x sigma sigma',
  sigma' = (update sigma x (default)) ->
  (int* x) -{ sigma }-> sigma'
| e_int_decl : forall a i x sigma sigma' sigma_final,
  a =[ sigma ]=> i ->
  sigma' = (update sigma x default) ->
  sigma_final = (update sigma' x (rint i)) ->
  (int x =' a) -{ sigma }-> sigma_final
| e_int_assign : forall a i x sigma sigma',
  a =[ sigma ]=> i ->
  sigma' = (update sigma x (rint i)) ->
  (x ::=n a) -{ sigma }-> sigma'
| e_bool_decl_null : forall a x sigma sigma',
  sigma' = (update sigma x (rbool false)) ->
  (boolean* a) -{ sigma }-> sigma'
| e_bool_decl : forall a i x sigma sigma',
  a ={ sigma }=> i ->
  sigma' = (update sigma x (rbool i)) ->
  (boolean x =' a) -{ sigma }-> sigma'
| e_bool_assign : forall a i x sigma sigma',
  a ={ sigma }=> i ->
  sigma' = (update sigma x (rbool i)) ->
  (x ::=b a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
  s1 -{ sigma }-> sigma1 ->
  s2 -{ sigma1 }-> sigma2 ->
  (s1 ;; s2) -{ sigma }-> sigma2
| e_break1 : forall s1 s2 sigma,
  s1 -{ sigma }-> sigma ->
  s2 -{ sigma }-> sigma ->
  (s1 ;; s2) -{ sigma }-> sigma
| e_break2 : forall s1 s2 sigma sigma1,
  s1 -{ sigma }-> sigma1 ->
  s2 -{ sigma1 }-> sigma1 ->
  (s1 ;; s2) -{ sigma }-> sigma1
| e_ifthen_false : forall b s1 sigma,
    b ={ sigma }=> false ->
    (Iff b Then s1) -{ sigma }-> sigma
| e_ifthen_true : forall b s1 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (Iff b Then s1) -{ sigma }-> sigma1
| e_ifthenelse_false : forall b s1 s2 sigma sigma2,
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma2 ->
    (If b Then s1 Else s2) -{ sigma }-> sigma2
| e_ifthenelse_true : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (If b Then s1 Else s2) -{ sigma }-> sigma1
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    whilethisdothat b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; whilethisdothat b s) -{ sigma }-> sigma' ->
    whilethisdothat b s -{ sigma }-> sigma'
| e_forfalse : forall e1 e2 e3 s sigma,
    e2 ={ sigma }=> false ->
    forthisdothat e1 e2 e3 s -{ sigma }-> sigma
| e_fortrue : forall e1 e2 e3 s sigma sigma',
    e2 ={ sigma }=> true ->
    (e1 ;; whilethisdothat e2 (s ;; e3)) -{ sigma }-> sigma' ->
    forthisdothat e1 e2 e3 s -{ sigma }-> sigma'
| e_break : forall stmt sigma,
    stmt -{ sigma }-> sigma
where "S -{ sigma }-> Sigma'" := (eval S sigma Sigma').

Hint Constructors aeval.
Hint Constructors beval.
Hint Constructors eval.

(*
Example ex1 :
  exists sigma',
  (
    int "i" =' 0;;
    While ("i" <=' 10)
    (
      "i" ::=n ("i" +' 1);;
      break;;
      "i" ::=n ("i" +' 1)
    )
  )-{ env }-> sigma' /\ sigma' "i" = rint 1.
Proof.
  eexists.
  split.
  - eapply e_seq.
    + eapply e_int_decl; eauto.
    + eapply e_whiletrue.
      * eapply e_lessequalthan; eauto.
      * eapply e_seq.
        ++ eapply e_seq.
          +++ eapply e_break2.
            ++++ eapply e_int_assign; eauto.
            ++++ eapply e_break.
          +++ eapply e_int_assign; eauto.
        ++ eapply e_whiletrue; eauto.
  - unfold update. simpl. reflexivity.
Qed.
*)





