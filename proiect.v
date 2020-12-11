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

Inductive Results :=
| err_undecl : Results
| err_assign : Results
| rint : ErrorInt -> Results
| rbool : ErrorBool -> Results
| default : Results.
Scheme Equality for Results.

Inductive AExp :=
| aint : Z -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| amax : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| apow : AExp -> AExp -> AExp.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| beq : AExp -> AExp -> BExp
| blt : AExp -> AExp -> BExp
| ble : AExp -> AExp -> BExp
| bgt : AExp -> AExp -> BExp
| bge : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Inductive Stmt :=
| assignment_int : string -> AExp -> Stmt
| assignment_bool : string -> BExp -> Stmt
| adecboolnull : string -> Stmt
| adecbool : string -> bool -> Stmt
| adecintnull : string -> Stmt
| adecint : string -> AExp -> Stmt
| adecarray : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| whilethisdothat : BExp -> Stmt -> Stmt
| forthisdothat : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| define_int : string -> AExp -> Stmt
| define_bool : string -> BExp -> Stmt
| case_list : Z -> Stmt -> Stmt  (* int -> sequence -> Stmt *)
| switch : AExp -> Stmt -> Stmt (* AExp -> case_list -> Stmt *)
| label : string -> Stmt -> Stmt
| goto : string -> Stmt.

Coercion aint : Z >-> AExp.
Coercion avar : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Notation "'min' '(' A ',' B ')'" := (amin A B) (at level 45).
Notation "'max' '(' A ',' B ')'" := (amax A B) (at level 45).
Notation "'pow' '(' A ',' B ')'" := (apow A B) (at level 45).

(* Verificari AExp *)
Check -2 +' 3.
Check -1 -' 5.
Check 2 *' -3.
Check 2 /' 0.
Check 5 %' 2.
Check min(1, 2).
Check max(3, 5).
Check pow(2, 10).

Notation "! A" := (bnot A) (at level 54).
Notation "A ==' B" := (beq A B) (at level 53).
Notation "A <' B" := (blt A B) (at level 53).
Notation "A <=' B" := (ble A B) (at level 53).
Notation "A >' B" := (bgt A B) (at level 53).
Notation "A >=' B" := (bge A B) (at level 53).

Check !btrue.
Check 1 ==' 1.
Check -1 <' 3.
Check 0 <=' 2.
Check 1 >' 0.
Check 2 >=' 2.

Notation "A '&&'' B" := (band A B) (at level 55).
Notation "A '||'' B" := (bor A B) (at level 55).

Check btrue &&' bfalse.
Check btrue ||' bfalse.

Notation "'boolean*' A" := (adecboolnull A) (at level 56).
Notation "'boolean' A =' B" := (adecbool A B) (at level 56).

Check boolean* "ok".
Check boolean "ok" =' false.

Notation "'int*' A" := (adecintnull A) (at level 50).
Notation "'int' A =' B" := (adecint A B) (at level 50).
Notation "'array' A '['' B '']'" := (adecarray A B) (at level 50).
Notation "X ::=n A" := (assignment_int X A) (at level 50).
Notation "X ::=b A" := (assignment_bool X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'Iff' A 'Then' B" := (ifthen A B) (at level 90).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 90).
Notation "'While' '(' A ')' '(' B ')'" := (whilethisdothat A B) (at level 90).
Notation "'For' '(' A ; B ; C ')' '(' D ')'" := (forthisdothat A B C D) (at level 90).
Notation "A :' B" := (label A B) (at level 90).

Check int* "sum".
Check int "sum" =' 0.
Check array "a" ['4'].
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
Definition update (env : Env) (v : string) (val : Results) : Env :=
  fun v' => if (eqb v v')
            then
              if (andb (CheckType (err_undecl) (env v')) (negb(CheckType (default) (val))))
              then err_undecl
              else
                if (andb (CheckType (err_undecl) (env v')) (CheckType (default) (val)))
                then default
                else
                  if (orb (CheckType (default) (env v')) (CheckType (val) (env v')))
                  then val
                  else err_assign
            else env v'.

Compute (env "x").
Compute (update (update env "x" (default)) "x" (rbool true) "x").

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











