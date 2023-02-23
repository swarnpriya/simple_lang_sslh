Require Import Nat.
Require Import String.
Require Import List.
Require Import Coq.Init.Datatypes PArray.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.

(********************************************************)

(* Syntax of language *)

(********************************************************)

(* Value *)

Definition value := nat.

(* Operators *)
Inductive bop : Type :=
| plus : bop
| minus : bop.

(* Boolean Operators *)
Inductive bool_op : Type :=
| equal : bool_op
| less_than : bool_op
| greater_than : bool_op.

Definition varr := string.
Definition var  := string.

(* Expressions *)
Inductive expr : Type :=
| Evar : var -> expr (* variable *)
| Ebop : bop -> expr -> expr -> expr (* operation *).
(*| Edeclassify: expr -> expr (* declassify *).*)

(* Boolean Expressions *)
Inductive bexpr : Type :=
| Ebool : bool_op -> expr -> expr -> bexpr.

Inductive arr_access : Type :=
| AA : varr -> expr -> arr_access (* a[e] *).

Definition declassify := bool.

(* Instructions *)
Inductive instr : Type :=
| Iempty : instr
| Iassgn : var -> declassify -> expr -> instr (* assignemnt x := e *)
| Iload : var -> declassify -> arr_access -> instr (* x := a[e] *)
| Istore : arr_access -> declassify -> expr -> instr  (* a[e] := e *) 
| Iif : bexpr -> seq instr -> seq instr -> instr (* conditional if b i i *).

Definition cmd := seq instr.

Definition map (A:Type) := string -> A.

Definition get_map {A:Type} (m:map A) (x:string) := m x.


(*Parameter update_map : forall {A:Type}, map A -> string -> A -> map A.*)

Definition update_map {A:Type} (m:map A) x v : map A := 
  fun y => if String.eqb x y then v else m y.

(* Register map *)
(* Maps registers to values *)
Definition regmap : Type := map value.

(* Signature of Array *)
Module Array.
   Parameter t : Type.
   Parameter get : t -> value -> value.
   Parameter set : t -> nat -> value -> t.
   Parameter get_length : t -> nat.
   Parameter get_index : t -> value -> nat.
End Array.


(* Memory *)
Definition mem : Type := map Array.t. 

(* State with no speculation *)
Record state_sf := State_sf {
  scmd_sf : cmd;
  rmap_sf : regmap;
  mmap_sf  : mem
}.

Definition eval_bop (o:bop) (v:value) (v':value) : value :=
  match o with 
  | plus => v + v'
  | minus => v - v'
  end.

Definition eval_bool_op (o:bool_op) (v:value) (v':value) : bool :=
  match o with 
  | equal => v == v'
  | less_than => v < v'
  | greater_than => v > v'
  end.

(* Semantic of expressions *)
Fixpoint sem_expr (s:state_sf) (e:expr) : value :=
  match e with 
  | Evar x => (rmap_sf s) x
  | Ebop o e e' => eval_bop o (sem_expr s e) (sem_expr s e')
  end.

Definition update_mem (m:mem) (a:varr) (n:nat) (v:value) := 
   let t := m a in
   let t' := Array.set t n v in
   update_map m a t'.

Definition update_rmap (r:regmap) (x:var) (v:value) :=
   update_map r x v.

Definition in_bound (m:mem) (a:varr) (i:nat) := 
  let av := m a in
  let n := Array.get_length av in 
  if i <= n then true else false.

(* Leakages *)
Inductive leakage : Type :=
| Lbool : bool -> leakage
| Lindex : nat -> leakage
| Ldeclassify : option value -> leakage
| Lempty : leakage.

(* Semantics of instructions without speculation *)
(* Small-step semantics (Single step for one instruction -- It produces seq of leakage *)
(* Extraction of declassify from leakage will give seq of option value *)
Inductive sem_instr : state_sf -> seq leakage -> state_sf -> Prop :=
| Iempty_sem : forall s c, 
  s.(scmd_sf) = Iempty :: c -> 
  sem_instr s 
  [::]
  {| scmd_sf := c; 
     rmap_sf := s.(rmap_sf);
     mmap_sf := s.(mmap_sf) |}
| Iassgn_sem : forall s x d e c, (* x := 0 *)
  s.(scmd_sf) = Iassgn x d e :: c ->  
  sem_instr s 
  (if d then [:: Ldeclassify (Some (sem_expr s e))] else [:: Lempty]) 
  {| scmd_sf := c; 
     rmap_sf := update_rmap s.(rmap_sf) x (sem_expr s e);
     mmap_sf := s.(mmap_sf) |}
(*| Iif_sem_true : forall s i1 i2 bop e1 e2,
  s.(stmt) = Iif (Ebool bop e1 e2) i1 i2 ->
  eval_bool_op bop (sem_expr s e1) (sem_expr s e2) = true ->
  sem_instr s (Lbool true) (with_stmt s i1)
| Iif_sem_false : forall s i1 i2 bop e1 e2,
  s.(stmt) = Iif (Ebool bop e1 e2) i1 i2 ->
  eval_bool_op bop (sem_expr s e1) (sem_expr s e2) = false ->
  sem_instr s (Lbool false) (with_stmt s i2)*)
| Iif_sem : forall s i1 i2 bop e1 e2 c,
  s.(scmd_sf) = Iif (Ebool bop e1 e2) i1 i2 :: c ->
  sem_instr s 
  [:: (Lbool (eval_bool_op bop (sem_expr s e1) (sem_expr s e2)))] 
  {| scmd_sf := (if (eval_bool_op bop (sem_expr s e1) (sem_expr s e2)) then i1 else i2) ++ c; 
     rmap_sf := s.(rmap_sf);
     mmap_sf := s.(mmap_sf) |}
| Iload_sem : forall s x d a e c,
  s.(scmd_sf) = Iload x d (AA a e) :: c ->
  sem_instr s 
  (if d then [:: Lindex (sem_expr s e); Ldeclassify (Some (Array.get (s.(mmap_sf) a) (sem_expr s e)))] else [:: Lindex (sem_expr s e)]) 
  {| scmd_sf := c; 
     rmap_sf := update_rmap s.(rmap_sf) x (Array.get (s.(mmap_sf) a) (sem_expr s e));
     mmap_sf := s.(mmap_sf)|}
| Istore_sem : forall s a e d e' c,
  s.(scmd_sf) = Istore (AA a e) d e' :: c ->
  sem_instr s
  (if d then [:: Lindex (sem_expr s e); Ldeclassify (Some (sem_expr s e'))] else [:: Lindex (sem_expr s e)])  
  {| scmd_sf := c; 
     rmap_sf := s.(rmap_sf);
     mmap_sf := update_mem s.(mmap_sf) a (sem_expr s e) (sem_expr s e') |}.

(* Multi step for instructions without spec *)
Inductive multi_step : state_sf -> seq (seq leakage) -> nat -> state_sf -> Prop :=
| sem_empty : forall s, multi_step s nil 0 s
| sem_seq : forall s l s' l' s'' n,
  sem_instr s l s' ->
  multi_step s' l' n s'' ->
  multi_step s (l :: l') (n + 1) s''.

Definition final_state (s:state_sf) : bool :=
match s.(scmd_sf) with 
| [::] => true
| _ => false
end.

(*Fixpoint inbound_instr (s:state_sf) (si:instr) {struct si}: Prop :=
match si with 
| Iassgn x e => True 
| Iload x (AA a e) => in_bound s.(mmap_sf) a (sem_expr s e) = true
| Istore (AA a e) e' => in_bound s.(mmap_sf) a (sem_expr s e) = true
| Iif b i i' => True
| Iseq i i' => inbound_instr s i /\ inbound_instr s i'
| Iempty => True
end.

Definition inbound_state (s:state_sf) : Prop :=
let si := s.(stmt_sf) in
inbound_instr s si.*)

Definition safe_state (s:state_sf) :=
final_state s = true \/ exists l s', sem_instr s l s'.











