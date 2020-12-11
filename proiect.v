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

Inductive Results :=
| rint : Z -> Results
| rbool : bool -> Results
| default : Results.
Scheme Equality for Results.

Inductive AExp :=
| aint : Z -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

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
| assignment : string -> AExp -> Stmt
| adecboolnull : string -> Stmt
| adecbool : string -> bool -> Stmt
| adecintnull : string -> Stmt
| adecint : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| whilethisdothat : BExp -> Stmt -> Stmt
| forthisdothat : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Coercion aint : Z >-> AExp.
Coercion avar : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).

Notation "! A" := (bnot A) (at level 54).
Notation "A ==' B" := (beq A B) (at level 53).
Notation "A <' B" := (blt A B) (at level 53).
Notation "A <=' B" := (ble A B) (at level 53).
Notation "A >' B" := (bgt A B) (at level 53).
Notation "A >=' B" := (bge A B) (at level 53).

Notation "A '&&'' B" := (band A B) (at level 55).
Notation "A '||'' B" := (bor A B) (at level 55).

Notation "'boolean*' A" := (adecboolnull A) (at level 56).
Notation "'boolean' A =' B" := (adecbool A B) (at level 56).

Notation "'int*' A" := (adecintnull A) (at level 50).
Notation "'int' A =' B" := (adecint A B) (at level 50).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'Iff' A 'Then' B" := (ifthen A B) (at level 90).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 90).
Notation "'While' '(' A ')' '(' B ')'" := (whilethisdothat A B) (at level 90).
Notation "'For' '(' A ; B ; C ')' '(' D ')'" := (forthisdothat A B C D) (at level 90).

Definition Env := string -> Results.

(* lookup *)
Definition env0 : Env := fun n => default.

(* update *)
Definition update (env : Env) (v : string) (val : Results) : Env :=
  fun v' => if (eqb v v')
            then val
            else (env v').


Inductive ErrorInt :=
  | err : ErrorInt
  | num : Z -> ErrorInt.

Definition plus_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err, _ => err
    | _, err => err
    | num v1, num v2 => num (v1 + v2)
    end.

Definition minus_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err, _ => err
    | _, err => err
    | num v1, num v2 => num (v1 + v2)
    end.

Definition mul_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err, _ => err
    | _, err => err
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err, _ => err
    | _, err => err
    | _, num 0 => err
    | num v1, num v2 => num (Z.div v1 v2)
    end.

Definition mod_err (n1 n2 : ErrorInt) : ErrorInt :=
  match n1, n2 with
    | err, _ => err
    | _, err => err
    | _, num 0 => err
    | num v1, num v2 => num (Z.modulo v1 v2)
    end.


