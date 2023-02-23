Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang.

Set Implicit Arguments.

(********************************************************)

(* Type System *)

(********************************************************)

Inductive level := 
| Secret 
| Public. 

Definition union_level (l1 : level) (l2 : level) : level :=
match l1, l2 with 
| Secret, _ => Secret 
| Public, l => l
end.

Definition sub_level (l1 : level) (l2 : level) : bool :=
match l1, l2 with 
| Secret, Public => false
| Public, Secret => true
| _, _ => true
end.

(* Typing enviornment *)
Definition partial_map (A:Type) := string -> option A.

Definition venv := partial_map level.

Definition aenv := partial_map level.

(* Type system for expressions *)
Inductive type_expr (VGamma:venv) : expr -> level -> Prop :=
| T_Evar : forall x T, 
  VGamma x = Some T -> 
  type_expr VGamma (Evar x) T
| T_Ebop : forall o e T e' T', 
  type_expr VGamma e T ->
  type_expr VGamma e' T' ->
  type_expr VGamma (Ebop o e e') (union_level T T').

(* Type system for array access *)
Inductive type_AA (VGamma:venv) (AGamma:aenv) : arr_access -> level -> Prop :=
| T_AA : forall a e T,
  AGamma a = Some T ->
  type_expr VGamma e Public ->
  type_AA VGamma AGamma (AA a e) T.

(* Type system for boolean expression *)
Inductive type_bexpr (VGamma:venv) : bexpr -> level -> Prop :=
| T_bexpr : forall o e1 e2 T1 T2,
  type_expr VGamma e1 T1 ->
  type_expr VGamma e2 T2 ->
  type_bexpr VGamma (Ebool o e1 e2) (union_level T1 T2).

(* Type system for instructions *)
Inductive type_cmd (VGamma:venv) (AGamma:aenv) : cmd -> Prop :=
| T_seq : forall i c,
  type_instr VGamma AGamma i ->
  type_cmd VGamma AGamma c ->
  type_cmd VGamma AGamma (i :: c)
| T_empty : 
  type_cmd VGamma AGamma [::]

with type_instr (VGamma:venv) (AGamma:aenv) : instr -> Prop :=
(* x := e *)
| T_assgn : forall x e T T',
  VGamma x = Some T ->
  type_expr VGamma e T' ->
  sub_level T' T = true ->
  type_instr VGamma AGamma (Iassgn x e)
(* x := a[e] *)
| T_load : forall x a T T',
  VGamma x = Some T ->
  type_AA VGamma AGamma a T' ->
  sub_level T' T = true ->
  type_instr VGamma AGamma (Iload x a)
(* a[e] := e *)
| T_store : forall e a T T',
  type_expr VGamma e T ->
  type_AA VGamma AGamma a T' ->
  sub_level T T' = true ->
  type_instr VGamma AGamma (Istore a e)
| T_if : forall b i i',
  type_bexpr VGamma b Public ->
  type_cmd VGamma AGamma i ->
  type_cmd VGamma AGamma i' ->
  type_instr VGamma AGamma (Iif b i i').
