Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang_spec.

Set Implicit Arguments.

(********************************************************)

(* Type System *)

(********************************************************)

Inductive vlevel := 
| Secret 
| Public
| PublicLoad. 

Inductive alevel :=
| ASecret
| APublic.

Definition union_vlevel (l1 : vlevel) (l2 : vlevel) : vlevel :=
match l1, l2 with 
| Secret, _ => Secret 
| Public, l => l
| PublicLoad, Secret => Secret
| PublicLoad, _ => PublicLoad
end.

Definition sub_vlevel (l1 : vlevel) (l2 : vlevel) : bool :=
match l1, l2 with 
| Secret, _ => false
| Public, l => true
| PublicLoad, Secret => true
| PublicLoad, _ => false
end.

Definition alevel_to_vlevel (l1 : alevel) : vlevel :=
match l1 with 
| ASecret => Secret
| APublic => PublicLoad
end.

(* Typing enviornment *)
Definition partial_map (A:Type) := string -> option A.

Definition venv := partial_map vlevel.

Definition aenv := partial_map alevel.

(* Type system for expressions *)
Inductive type_expr (VGamma:venv) : expr -> vlevel -> Prop :=
| T_Evar : forall x T, 
  VGamma x = Some T -> 
  type_expr VGamma (Evar x) T
| T_Ebop : forall o e T e' T', 
  type_expr VGamma e T ->
  type_expr VGamma e' T' ->
  type_expr VGamma (Ebop o e e') (union_vlevel T T').

(* Type system for array access *)
Inductive type_AA (VGamma:venv) (AGamma:aenv) : arr_access -> alevel -> Prop :=
| T_AA : forall a e T,
  AGamma a = Some T ->
  type_expr VGamma e Public ->
  type_AA VGamma AGamma (AA a e) T.

(* Type system for boolean expression *)
Inductive type_bexpr (VGamma:venv) : bexpr -> vlevel -> Prop :=
| T_bexpr : forall o e1 e2 T1 T2,
  type_expr VGamma e1 T1 ->
  type_expr VGamma e2 T2 ->
  type_bexpr VGamma (Ebool o e1 e2) (union_vlevel T1 T2).

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
  sub_vlevel T' T = true ->
  type_instr VGamma AGamma (Iassgn x e)
(* x := a[e] *)
| T_load : forall x a T T',
  VGamma x = Some T ->
  type_AA VGamma AGamma a T' ->
  sub_vlevel (alevel_to_vlevel T') T ->
  type_instr VGamma AGamma (Iload x a)
(*(* x := a[e] -- public load *)
| T_pubload : forall x a,
  VGamma x = Some PublicLoad ->
  type_AA VGamma AGamma a Public ->
  type_instr VGamma AGamma (Iload x a)*)
(* a[e] := e *)
| T_store : forall e a T T',
  type_expr VGamma e T ->
  type_AA VGamma AGamma a T' ->
  sub_vlevel T (alevel_to_vlevel T') ->
  type_instr VGamma AGamma (Istore a e)
| T_if : forall b i i',
  type_bexpr VGamma b Public ->
  type_cmd VGamma AGamma i ->
  type_cmd VGamma AGamma i' ->
  type_instr VGamma AGamma (Iif b i i')
| T_protect : forall x y T, (*x := y ---> protect x y*)
  (*VGamma x = Some PublicLoad ->
  VGamma y = Some T ->
  sub_vlevel T PublicLoad = true ->
  type_instr VGamma AGamma (Iprotect x y).*)
  VGamma x = Some Public ->
  VGamma y = Some T ->
  sub_vlevel T PublicLoad = true ->
  type_instr VGamma AGamma (Iprotect x y).



